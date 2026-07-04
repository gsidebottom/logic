#!/usr/bin/env python3
"""Structural analysis of flip-graph landings: are they reducible, or
flip-isolated sinks? Answers why a descent plateaus at a given rank.

For a sample of saved schemes at one rank, computes the pairwise
shared-factor (agreement) histogram. Agreement >= 1 is required for ANY
flip to apply; agreement >= 2 means an immediate merge (rank -1). A
scheme with all-zero agreements is a flip-graph SINK: no flip acts on it,
so pure flip/equalization search cannot reduce it — escaping needs
rank-increasing (plus) transitions through a different basin.

Usage: python3 flip_analyze.py DIR N1 N2 N3 R [--sample K]
"""
import glob
import random
import sys
from collections import Counter

from brent import var_counts


def summands(bits, n1, n2, n3, r):
    na, nb, _ = var_counts(n1, n2, n3, r)
    sa, sb, sg = n1 * n2, n2 * n3, n1 * n3
    out = []
    for m in range(r):
        a = b = g = 0
        for k in range(sa):
            a |= bits[m * sa + k] << k
        for k in range(sb):
            b |= bits[na + m * sb + k] << k
        for k in range(sg):
            g |= bits[na + nb + m * sg + k] << k
        out.append((a, b, g))
    return out


def agree(x, y):
    return (x[0] == y[0]) + (x[1] == y[1]) + (x[2] == y[2])


def main():
    d, n1, n2, n3, r = (sys.argv[1], *map(int, sys.argv[2:6]))
    k = int(sys.argv[sys.argv.index("--sample") + 1]) \
        if "--sample" in sys.argv else 80
    files = glob.glob(f"{d}/r{r}-*.bits") or glob.glob(f"{d}/*.bits")
    random.Random(1).shuffle(files)
    files = files[:k]
    hist = Counter()
    isolated = 0
    reducible = 0
    for f in files:
        s = summands([int(c) for c in open(f).read().strip()],
                     n1, n2, n3, r)
        rr = len(s)
        any_share = has_merge = False
        for i in range(rr):
            for j in range(i + 1, rr):
                a = agree(s[i], s[j])
                hist[a] += 1
                if a >= 1:
                    any_share = True
                if a >= 2:
                    has_merge = True
        isolated += not any_share
        reducible += has_merge
    print(f"rank {r}: {len(files)} schemes")
    print(f"  pairwise agreement histogram: {dict(sorted(hist.items()))}")
    print(f"  flip-isolated (0 shared factors anywhere): "
          f"{isolated}/{len(files)}")
    print(f"  immediately reducible (a pair shares >=2): "
          f"{reducible}/{len(files)}")


if __name__ == "__main__":
    main()
