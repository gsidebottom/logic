#!/usr/bin/env python3
"""summarize_r363_points.py RESULT: the table of run_r363_points.sh's output.

Per size, precision and plan: the error at DPS's point against the exact product (dps, geometric mean over the
seeds, and as a multiple of the GEMM's), and the error of h (blocks mixed by the reflection (2/3) J - I) and of m
(mixed by a minimizer's rotations) over dps's, seed by seed: geometric mean [min, max].  Then the same for the
minimum time.
"""
import math, re, sys
from collections import defaultdict

HEAD = re.compile(r"^### (\w+) n=(\d+) (\w) seed=(\d+)")
ROW = re.compile(r"n=(\d+)\s+f(32|64)\s+min\s+([\d.]+) s.*?plan (\S+).*?err64 ([\d.e+-]+)")

def gm(xs):
    return math.exp(sum(math.log(x) for x in xs) / len(xs))

def main():
    err = defaultdict(dict)    # (n, prec, plan)[(variant, seed)] = error
    tim = defaultdict(dict)
    order = []
    v = seed = None
    for ln in open(sys.argv[1]):
        m = HEAD.match(ln)
        if m:
            v, seed = m.group(1), int(m.group(4)); continue
        m = ROW.search(ln)
        if m and v:
            key = (int(m.group(1)), "f" + m.group(2), m.group(4))
            if key not in err: order.append(key)
            err[key][(v, seed)] = float(m.group(5)); tim[key][(v, seed)] = float(m.group(3))
    print(f"{'n':>6} {'prec':4} {'plan':22} {'seeds':>5} {'dps err':>10} {'x GEMM':>7}   {'h / dps':>22}   {'m / dps':>22}   {'m / h':>22}   time: h, m over dps")
    for key in order:
        e, t = err[key], tim[key]
        seeds = sorted({s for (_, s) in e})
        seeds = [s for s in seeds if all((x, s) in e for x in ("dps", "h", "m"))]
        if not seeds: continue
        base = gm([e[("dps", s)] for s in seeds])
        g = (key[0], key[1], "G")
        xg = "" if key[2] == "G" else f"{gm([e[('dps', s)] / err[g][('dps', s)] for s in seeds]):7.2f}"
        def col(a, b):
            r = [e[(a, s)] / e[(b, s)] for s in seeds]
            return f"{gm(r):6.3f} [{min(r):5.3f}, {max(r):5.3f}]"
        tr = lambda a: min(t[(a, s)] for s in seeds) / min(t[("dps", s)] for s in seeds)
        print(f"{key[0]:>6} {key[1]:4} {key[2]:22} {len(seeds):>5} {base:10.3e} {xg:>7}   {col('h', 'dps'):>22}   {col('m', 'dps'):>22}   {col('m', 'h'):>22}   {tr('h'):5.3f} {tr('m'):5.3f}")

if __name__ == "__main__":
    main()
