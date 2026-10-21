#!/usr/bin/env python3
"""Evaluate orbit candidates (orbit48.py output) with PLinOpt's tools: for
each candidate and side, the best base-optimizer program over several runs
(direct for L and R; direct / kernel-transposed for P), counted by
SLPchecker as additions + multiplications; then, for the top candidates by
that total, the pair-refinement loop (prune_loop.py) on each side.

Usage: evalcand.py CANDIDATES_CSV OUTDIR --bin PLINOPT_BIN --path GNU_PATH
         [--runs 6] [--loops 200] [--refine 3] [--rounds 12]
Writes OUTDIR/eval.csv (quick totals) and OUTDIR/refined.csv.
"""
import os
import re
import subprocess
import sys
import time

H = os.path.dirname(os.path.abspath(__file__))


def opt(name, default, cast):
    a = sys.argv
    if name in a:
        i = a.index(name)
        v = cast(a[i + 1])
        del a[i:i + 2]
        return v
    return default


def count(bin_dir, sms, slp_text, env):
    r = subprocess.run([f"{bin_dir}/SLPchecker", "-M", sms], input=slp_text, capture_output=True, text=True, env=env)
    o = re.sub(r"\x1b\[[0-9;]*m", "", r.stdout + r.stderr)
    m = re.search(r"SUCCESS.*?<(\d+), (\d+)>", o)
    return (int(m.group(1)), int(m.group(2))) if m else None


def best_program(bin_dir, sms, runs, loops, env, transposed_modes):
    best = None
    for _ in range(runs):
        modes = ["direct"] + (["kernel"] if transposed_modes else [])
        for mode in modes:
            if mode == "direct":
                p = subprocess.run([f"{bin_dir}/optimizer", "-O", str(loops), sms], capture_output=True, text=True, env=env)
                slp = p.stdout
            else:
                t = subprocess.run([f"{bin_dir}/matrix-transpose", sms], capture_output=True, text=True, env=env).stdout
                o = subprocess.run([f"{bin_dir}/optimizer", "-K", "-O", str(loops)], input=t, capture_output=True, text=True, env=env).stdout
                slp = subprocess.run([f"{bin_dir}/transpozer"], input=o, capture_output=True, text=True, env=env).stdout
            c = count(bin_dir, sms, slp, env)
            if c and (best is None or sum(c) < sum(best[0])):
                best = (c, slp)
    return best


def main():
    bin_dir = opt("--bin", None, str)
    gnu = opt("--path", "", str)
    runs = opt("--runs", 6, int)
    loops = opt("--loops", 200, int)
    nref = opt("--refine", 3, int)
    rounds = opt("--rounds", 12, int)
    csv_in, outdir = sys.argv[1], sys.argv[2]
    os.makedirs(outdir, exist_ok=True)
    env = dict(os.environ)
    if gnu:
        env["PATH"] = gnu + ":" + env["PATH"]
    cands = [ln.rstrip("\n").split(",") for ln in open(csv_in) if not ln.startswith("rank,")]
    rows = ["prefix,floor,quickL,quickR,quickP,quick_total"]
    quick = []
    def tag(pre):  # unique file tag: parent directory + basename
        return os.path.basename(os.path.dirname(pre)) + "_" + os.path.basename(pre)

    for c in cands:
        pre, floor = c[-1], c[1]
        t0 = time.time()
        res = {}
        for side in "LRP":
            sms = f"{pre}_{side}.sms"
            b = best_program(bin_dir, sms, runs, loops, env, transposed_modes=(side == "P"))
            res[side] = b
            open(os.path.join(outdir, f"{tag(pre)}_{side}.slp"), "w").write(b[1] if b else "")
        tot = sum(sum(res[s][0]) for s in "LRP") if all(res[s] for s in "LRP") else None
        cells = [f"{sum(res[s][0])}" if res[s] else "?" for s in "LRP"]
        rows.append(f"{pre},{floor},{cells[0]},{cells[1]},{cells[2]},{tot}")
        quick.append((tot if tot is not None else 10 ** 9, pre, res))
        print(f"{tag(pre)}: floor {floor}, quick L/R/P {cells} total {tot} ({time.time() - t0:.0f}s)", flush=True)
    open(os.path.join(outdir, "eval.csv"), "w").write("\n".join(rows) + "\n")
    quick.sort(key=lambda t: t[0])
    rows2 = ["prefix,refinedL,refinedR,refinedP,refined_total"]
    for tot, pre, res in quick[:nref]:
        parts = []
        for side in "LRP":
            slp = os.path.join(outdir, f"{tag(pre)}_{side}.slp")
            wd = os.path.join(outdir, f"refine_{tag(pre)}_{side}")
            subprocess.run([sys.executable, f"{H}/prune_loop.py", "--slp", slp, "--sms", f"{pre}_{side}.sms", "--bin", bin_dir, "--out", wd, "--rounds", str(rounds), "--loops", "100", "--mode", "p", "--path", gnu], capture_output=True, text=True, env=env, timeout=14400)
            best = os.path.join(wd, "best.slp")
            c = count(bin_dir, f"{pre}_{side}.sms", open(best).read(), env) if os.path.exists(best) else None
            parts.append(sum(c) if c else None)
        total = sum(parts) if all(p is not None for p in parts) else None
        rows2.append(f"{pre},{parts[0]},{parts[1]},{parts[2]},{total}")
        print(f"refined {tag(pre)}: {parts} total {total}", flush=True)
    open(os.path.join(outdir, "refined.csv"), "w").write("\n".join(rows2) + "\n")


if __name__ == "__main__":
    main()
