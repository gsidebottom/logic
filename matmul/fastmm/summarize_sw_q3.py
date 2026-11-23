#!/usr/bin/env python3
"""summarize_sw_q3.py RESULT: the table of run_sw_q3.sh's output.

Per size, precision and plan: the dyadic point's error against the exact product (dps7, geometric mean over the
seeds, and as a multiple of the GEMM's), and the error of dps7d (the dyadic point as direct sums) and of q3 (the
Q(sqrt 3) point) over dps7's, seed by seed: geometric mean [min, max].  Then the same for the minimum time.
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
    print(f"{'n':>6} {'prec':4} {'plan':22} {'seeds':>5} {'dps7 err':>10} {'x GEMM':>7}   {'dps7d / dps7':>22}   {'q3 / dps7':>22}   {'q3 / dps7d':>22}   time: dps7d, q3 over dps7")
    for key in order:
        e, t = err[key], tim[key]
        seeds = sorted({s for (_, s) in e})
        seeds = [s for s in seeds if all((x, s) in e for x in ("dps7", "dps7d", "q3"))]
        if not seeds: continue
        base = gm([e[("dps7", s)] for s in seeds])
        g = (key[0], key[1], "G")
        xg = "" if key[2] == "G" else f"{gm([e[('dps7', s)] / err[g][('dps7', s)] for s in seeds]):7.2f}"
        def col(a, b):
            r = [e[(a, s)] / e[(b, s)] for s in seeds]
            return f"{gm(r):6.3f} [{min(r):5.3f}, {max(r):5.3f}]"
        tr = lambda a: min(t[(a, s)] for s in seeds) / min(t[("dps7", s)] for s in seeds)
        print(f"{key[0]:>6} {key[1]:4} {key[2]:22} {len(seeds):>5} {base:10.3e} {xg:>7}   {col('dps7d', 'dps7'):>22}   {col('q3', 'dps7'):>22}   {col('q3', 'dps7d'):>22}   {tr('dps7d'):5.3f} {tr('q3'):5.3f}")

if __name__ == "__main__":
    main()
