#!/opt/homebrew/bin/python3
"""Deepen one point: run Patel's LNS (patel_phase.py) with several seeds and a
long budget on each side -- L and R from their current best programs, P
from its current best P^T program -- then re-verify every result with
SLPchecker against the point's matrices (PLinOpt counts), assemble the
cheapest triple and check it exactly with ../slp48check.py.

Usage: deepen.py --sms PREFIX --L L.slp --R R.slp --Pt Pt.slp --out DIR
       [--seeds 4] [--wall 1800] [--procs 12] [--temperature 0.35] [--tabu 1024]
Programs may be in PLinOpt's or Patel's syntax (his parser reads both).
"""
import argparse
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sweep as S  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sms", required=True, help="matrix prefix: PREFIX_{L,R,P}.sms")
    ap.add_argument("--L", required=True)
    ap.add_argument("--R", required=True)
    ap.add_argument("--Pt", required=True, help="program for P^T (48 outputs from 16 inputs)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--seeds", type=int, default=4)
    ap.add_argument("--seed0", type=int, default=11)
    ap.add_argument("--wall", type=float, default=1800)
    ap.add_argument("--procs", type=int, default=12)
    ap.add_argument("--temperature", type=float, default=0.35)
    ap.add_argument("--tabu", type=int, default=1024)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    sms = {"L": f"{a.sms}_L.sms", "R": f"{a.sms}_R.sms", "P": f"{a.sms}_P.sms"}
    progs = {"L": a.L, "R": a.R, "Pt": a.Pt}
    # starting costs (PLinOpt): the given programs, translated if needed
    start = {}
    for side in ("L", "R", "Pt"):
        t = S.translate(progs[side])
        c = S.slpcheck(sms["P"], S.transpose(t)) if side == "Pt" else S.slpcheck(sms[side], t)
        assert c, f"input program for {side} does not verify"
        start[side] = sum(c)
    print(f"start: L {start['L']} R {start['R']} P {start['Pt']} = {sum(start.values())}", flush=True)

    def one(job):
        side, seed = job
        out = os.path.join(a.out, f"{side}_s{seed}")
        cmd = [S.PY, S.PHASE, "--slp", progs[side], "--n", "16", "--seed", str(seed), "--wall", str(a.wall),
               "--out", out, "--log-seconds", "300", "--temperature", str(a.temperature), "--tabu", str(a.tabu),
               "--plinopt-model"]
        with open(out + ".log", "w") as log:
            subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, text=True, timeout=a.wall + 900)
        best = os.path.join(out, "best.slp")
        if not os.path.exists(best):
            return side, seed, None, None
        t = S.translate(best)
        c = S.slpcheck(sms["P"], S.transpose(t)) if side == "Pt" else S.slpcheck(sms[side], t)
        return side, seed, (sum(c) if c else None), best

    jobs = [(side, a.seed0 + i) for side in ("L", "R", "Pt") for i in range(a.seeds)]
    best = {side: (start[side], progs[side]) for side in ("L", "R", "Pt")}
    with ThreadPoolExecutor(a.procs) as pool:
        for side, seed, cost, path in pool.map(one, jobs):
            print(f"  {side} seed {seed}: {cost}", flush=True)
            if cost is not None and cost < best[side][0]:
                best[side] = (cost, path)
    for side in ("L", "R", "Pt"):
        t = S.translate(best[side][1])
        if side == "Pt":
            t = S.transpose(t)
        open(os.path.join(a.out, f"{side[0]}.slp"), "w").write(t)
    total = sum(b[0] for b in best.values())
    print(f"best: L {best['L'][0]} R {best['R'][0]} P {best['Pt'][0]} = {total} (from {start}) -> {a.out}/{{L,R,P}}.slp", flush=True)
    r = subprocess.run([sys.executable, os.path.join(os.path.dirname(HERE), "slp48check.py"), "--dir", a.out], capture_output=True, text=True)
    print(r.stdout.strip(), flush=True)
    sys.exit(r.returncode)


if __name__ == "__main__":
    main()
