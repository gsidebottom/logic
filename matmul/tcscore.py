#!/usr/bin/env python3
"""Batch EXACT re-scorer: exact sides + exact transposition C over a
set of representative .bits files.  All prior campaign totals used
GREEDY C (an upper bound); this recomputes the true additive
complexity per representative and flags any <= a cutoff.

Usage: tcscore.py DIR_or_files... [--cutoff 55] [--models 24]
"""
import glob
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from brent import verify_bits
from tcmin import score_exact

DIMS = (3, 3, 3, 23)


def main():
    argv = sys.argv[1:]
    cutoff = 55
    models = 24
    if "--cutoff" in argv:
        i = argv.index("--cutoff"); cutoff = int(argv[i + 1]); del argv[i:i + 2]
    if "--models" in argv:
        i = argv.index("--models"); models = int(argv[i + 1]); del argv[i:i + 2]
    paths = []
    for a in argv:
        if a.startswith("--"):
            continue
        paths += sorted(glob.glob(f"{a}/*.bits")) if "/" in a and \
            a.endswith("/") or (not a.endswith(".bits")) else [a]
    # normalize: if a is a dir, glob it
    real = []
    for a in [x for x in argv if not x.startswith("--")]:
        import os
        if os.path.isdir(a):
            real += sorted(glob.glob(f"{a}/*.bits"))
        else:
            real.append(a)
    best_overall = (10 ** 9, None)
    n = 0
    for p in real:
        try:
            bits = [int(c) for c in open(p).read().split()[-1].strip()]
        except Exception:
            continue
        if verify_bits(bits, *DIMS) != 0:
            continue
        n += 1
        res = score_exact(bits, DIMS, models)
        if not res:
            continue
        tot, A, B, C, mi = res
        if tot < best_overall[0]:
            best_overall = (tot, (p, A, B, C, mi))
        if tot <= cutoff:
            print(f"HIT {tot} = {A}+{B}+{C} (m{mi})  {p}", flush=True)
    tot, info = best_overall
    print(f"scored {n} reps; best EXACT total {tot}"
          + (f" = {info[1]}+{info[2]}+{info[3]} (m{info[4]}) {info[0]}"
             if info else ""), flush=True)


if __name__ == "__main__":
    main()
