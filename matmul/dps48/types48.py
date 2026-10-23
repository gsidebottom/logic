#!/usr/bin/env python3
"""A. Sedoglavic's 'type' of a <4x4x4> decomposition (his item 5): for each product, the
ranks of its three factor matrices [rank a, rank b, rank c], with a = row of L, b = row of R,
c = column of P, each read as a 4x4 matrix.  Prints, per scheme, how many products have each
type, the summed type, and how many factors of each rank every slot has.

  types48.py NAME=PREFIX ...     (PREFIX_{L,R,P}.sms; P is 16 x rank)
"""
import sys
from collections import Counter
from fractions import Fraction


def read_sms(path):
    with open(path) as f:
        rows, cols = map(int, f.readline().split()[:2])
        M = [[Fraction(0)] * cols for _ in range(rows)]
        for line in f:
            t = line.split()
            if len(t) != 3:
                continue
            i, j = int(t[0]), int(t[1])
            if i == 0 and j == 0:
                break
            M[i - 1][j - 1] += Fraction(t[2])
    return M


def rank(M):
    m = [row[:] for row in M]
    r = 0
    for c in range(len(m[0])):
        p = next((k for k in range(r, len(m)) if m[k][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        for k in range(len(m)):
            if k != r and m[k][c] != 0:
                f = m[k][c] / m[r][c]
                m[k] = [x - f * y for x, y in zip(m[k], m[r])]
        r += 1
    return r


def as4(v):
    return [v[4 * r:4 * r + 4] for r in range(4)]


def types(prefix):
    L, R, P = (read_sms(f"{prefix}_{s}.sms") for s in "LRP")
    Pc = [list(col) for col in zip(*P)]
    return [(rank(as4(L[i])), rank(as4(R[i])), rank(as4(Pc[i]))) for i in range(len(L))]


def main():
    for arg in sys.argv[1:]:
        name, prefix = arg.split("=", 1)
        ty = types(prefix)
        hist = Counter(ty)
        per_slot = [Counter(t[s] for t in ty) for s in range(3)]
        print(f"{name}: rank {len(ty)}, type sum {sum(map(sum, ty))}")
        print("  types: " + ", ".join(f"{list(k)} x{v}" for k, v in sorted(hist.items())))
        print("  factor ranks per slot (L, R, P): " + "; ".join(
            " ".join(f"r{k}:{v}" for k, v in sorted(c.items())) for c in per_slot))


if __name__ == "__main__":
    main()
