#!/opt/homebrew/bin/python3
"""Successive-halving sweep of Patel's phase LNS (via patel_phase.py) over the
orbit48 pool of rank-48 sparse points: L and R directly, P through its
transpose (Tellegen, +32).  Every count reported is PLinOpt's (SLPchecker
against the candidate's own matrices, after translating his syntax).

Stages: A = all candidates, short; B = best --a-keep, longer, continuing from
the stage-A programs; C = best --b-keep, longest, two seeds.

Usage: sweep.py --out DIR [--pool pool_sample.csv] [--evaldir eval_pool]
       [--procs 12] [--a-seconds 60] [--b-seconds 300] [--c-seconds 1200]
       [--a-keep 20] [--b-keep 5] [--limit N]
"""
import argparse
import csv
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

SP = os.environ.get("R48_SCRATCH", "/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad")  # run directories (scratch)
BIN = os.environ.get("PLINOPT_BIN", f"{SP}/plinopt-run/bin")  # SLPchecker, transpozer, optimizer, matrix-transpose
PY = "/opt/homebrew/bin/python3"
ENGINE = os.environ.get("LNS_ENGINE", "rust")  # "rust": ../../../target/release/lns48; "python": patel_phase.py on Patel's code
LNS48 = os.environ.get("LNS48_BIN", os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))), "target", "release", "lns48"))
NAIVE = os.environ.get("LNS_NAIVE", "0") == "1"
# FIXED_P = cost: the output map is fixed (e.g. P carried with a known program), so only
# L and R are searched and P is charged this cost
FIXED_P = int(os.environ.get("FIXED_P", "0"))
SIDES = ("L", "R") if FIXED_P else ("L", "R", "Pt")  # rust engine: seed from the matrix alone (no PLinOpt optimizer pass)
HERE = os.path.dirname(os.path.abspath(__file__))
PHASE = os.path.join(HERE, "patel_phase.py")
sys.path.insert(0, os.path.dirname(HERE))
import slp48check as C  # noqa: E402


def run(cmd, inp=None, timeout=600):
    r = subprocess.run(cmd, input=inp, capture_output=True, text=True, timeout=timeout)
    return re.sub(r"\x1b\[[0-9;]*m", "", r.stdout + r.stderr), r.stdout


def slpcheck(sms, text):
    o, _ = run([f"{BIN}/SLPchecker", "-M", sms], text)
    m = re.search(r"SUCCESS.*?<(\d+), (\d+)>", o)
    return (int(m.group(1)), int(m.group(2))) if m else None


def strip(text):
    return "\n".join(ln for ln in text.splitlines() if ln.strip() and not ln.lstrip().startswith("#")) + "\n"


def translate(path):
    prog = C.parse(open(path).read())
    n_in = 1 + max(int(m) for _, rhs in prog for m in re.findall(r"\bi(\d+)\b", rhs))
    return "\n".join(C.emit_plinopt(prog, n_in)) + "\n"


def transpose(text):
    _, out = run([f"{BIN}/transpozer"], text)
    return strip(out)


class Cand:
    def __init__(self, prefix, floor, tag, work):
        self.prefix, self.floor, self.tag = prefix, floor, tag
        self.dir = os.path.join(work, tag)
        os.makedirs(self.dir, exist_ok=True)
        self.sms = {s: f"{prefix}_{s}.sms" for s in "LRP"}
        self.sms["Pt"] = os.path.join(self.dir, "Pt.sms")
        self.seed_prog = {}   # side -> path of the current best program (his or PLinOpt syntax)
        self.cost = {}        # side -> PLinOpt count of the current best (P cost for Pt)
        self.ok = True

    def stage_inputs(self, evaldir):
        if ENGINE == "rust" and NAIVE:
            _, t = run([f"{BIN}/matrix-transpose", self.sms["P"]])
            open(self.sms["Pt"], "w").write(t)
            for side in ("L", "R", "Pt"):
                self.seed_prog[side] = None
                self.cost[side] = 10 ** 6
            if FIXED_P:
                self.cost["Pt"] = FIXED_P
            return
        for s in "LR":
            src = f"{evaldir}/{self.tag}_{s}.slp"
            dst = os.path.join(self.dir, f"seed_{s}.slp")
            open(dst, "w").write(strip(open(src).read()))
            c = slpcheck(self.sms[s], open(dst).read())
            if not c:
                self.ok = False
                return
            self.seed_prog[s], self.cost[s] = dst, sum(c)
        _, t = run([f"{BIN}/matrix-transpose", self.sms["P"]])
        open(self.sms["Pt"], "w").write(t)
        best = None
        for _ in range(2):
            _, o = run([f"{BIN}/optimizer", "-O", "50", self.sms["Pt"]], timeout=900)
            o = strip(o)
            c = slpcheck(self.sms["Pt"], o)
            if c and (best is None or sum(c) < best[0]):
                best = (sum(c), o)
        if best is None:
            self.ok = False
            return
        dst = os.path.join(self.dir, "seed_Pt.slp")
        open(dst, "w").write(best[1])
        self.seed_prog["Pt"], self.cost["Pt"] = dst, best[0] + 32

    def total(self):
        return self.cost["L"] + self.cost["R"] + self.cost["Pt"]


def job(cand, side, seed, wall, stage):
    out = os.path.join(cand.dir, f"{stage}_{side}_s{seed}")
    if ENGINE == "rust":
        cmd = [LNS48, "--sms", cand.sms[side], "--out", out, "--wall", str(wall), "--seeds", "1", "--seed", str(seed), "--log", "1e9"]
        if cand.seed_prog.get(side):
            cmd += ["--slp", cand.seed_prog[side]]
    else:
        cmd = [PY, PHASE, "--slp", cand.seed_prog[side], "--n", "16", "--seed", str(seed), "--wall", str(wall),
               "--out", out, "--log-seconds", "3600", "--plinopt-model"]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=wall + 600)
        if r.returncode != 0:
            open(out + ".err", "w").write(r.stdout + r.stderr)
            return cand, side, None, None
    except subprocess.TimeoutExpired:
        return cand, side, None, None
    best = os.path.join(out, "best.slp")
    if not os.path.exists(best):
        return cand, side, None, None
    t = translate(best)
    if side == "Pt":
        c = slpcheck(cand.sms["P"], transpose(t))
        cost = sum(c) if c else None
    else:
        c = slpcheck(cand.sms[side], t)
        cost = sum(c) if c else None
    return cand, side, cost, best


def stage(cands, name, wall, seeds, pool, log):
    jobs = [(c, s, sd) for c in cands for s in SIDES for sd in seeds]
    t0 = time.time()
    done = 0
    for cand, side, cost, best in pool.map(lambda j: job(j[0], j[1], j[2], wall, name), jobs):
        done += 1
        if cost is not None and cost < cand.cost[side]:
            cand.cost[side], cand.seed_prog[side] = cost, best
        if cost is None:
            log.write(f"{name},{cand.tag},{side},FAILED\n")
        if done % 12 == 0:
            print(f"  {name}: {done}/{len(jobs)} jobs, {time.time() - t0:.0f}s", flush=True)
    cands.sort(key=lambda c: (c.total(), c.tag))
    print(f"stage {name} ({wall}s x {len(seeds)} seeds) leaderboard:", flush=True)
    for c in cands[:10]:
        print(f"  {c.total():4d}  L {c.cost['L']:3d}  R {c.cost['R']:3d}  P {c.cost['Pt']:3d}  floor {c.floor}  {c.tag}", flush=True)
    with open(log.name.replace(".log", f"_{name}.csv"), "w") as f:
        f.write("tag,floor,L,R,P,total\n")
        for c in cands:
            f.write(f"{c.tag},{c.floor},{c.cost['L']},{c.cost['R']},{c.cost['Pt']},{c.total()}\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--pool", default=f"{SP}/r48/pool_sample.csv")
    ap.add_argument("--evaldir", default=f"{SP}/r48/eval_pool")
    ap.add_argument("--procs", type=int, default=12)
    ap.add_argument("--a-seconds", type=float, default=60)
    ap.add_argument("--b-seconds", type=float, default=300)
    ap.add_argument("--c-seconds", type=float, default=1200)
    ap.add_argument("--a-keep", type=int, default=20)
    ap.add_argument("--b-keep", type=int, default=5)
    ap.add_argument("--limit", type=int, default=0)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    rows = list(csv.DictReader(open(a.pool)))
    if a.limit:
        rows = rows[:a.limit]
    cands = []
    for r in rows:
        pre = r["prefix"]
        tag = os.path.basename(os.path.dirname(pre)) + "_" + os.path.basename(pre)
        cands.append(Cand(pre, r["floor"], tag, a.out))
    print(f"{len(cands)} candidates; staging inputs (quick L/R programs, P^T seeds)...", flush=True)
    with ThreadPoolExecutor(a.procs) as pool:
        list(pool.map(lambda c: c.stage_inputs(a.evaldir), cands))
        cands = [c for c in cands if c.ok]
        cands.sort(key=lambda c: (c.total(), c.tag))
        print(f"{len(cands)} staged; seed totals (PLinOpt): best {cands[0].total()} ({cands[0].tag}), worst {cands[-1].total()}", flush=True)
        log = open(os.path.join(a.out, "sweep.log"), "a")
        stage(cands, "A", a.a_seconds, [1], pool, log)
        stage(cands[:a.a_keep], "B", a.b_seconds, [2], pool, log)
        stage(cands[:a.b_keep], "C", a.c_seconds, [3, 4], pool, log)
    print("done", flush=True)


if __name__ == "__main__":
    main()
