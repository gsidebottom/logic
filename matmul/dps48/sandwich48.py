#!/usr/bin/env python3
"""Random de Groote sandwich variants of a rational <4x4x4:48> LRP
triple: conjugate by (P, Q, R) drawn from signed permutations times
dyadic diagonals, Brent-check each candidate exactly (Fractions),
primitive-normalize, and export .sms instances for the checker-gated
PLinOpt protocol.  The orbit x pipeline product search: their
optimizer's depth, our gauge breadth.
Usage: sandwich48.py SRCDIR OUTDIR N [seed]
"""
import os
import random
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from variants48 import parse_sms, brent_ok, primitive_gauge, write_sms


def mat4_mul(x, y):
    return [[sum(x[i][k] * y[k][j] for k in range(4)) for j in range(4)]
            for i in range(4)]


def mat4_inv(m):
    # Gauss-Jordan over Fractions
    a = [row[:] + [Fraction(int(i == j)) for j in range(4)]
         for i, row in enumerate(m)]
    for col in range(4):
        piv = next((r for r in range(col, 4) if a[r][col] != 0), None)
        if piv is None:
            return None
        a[col], a[piv] = a[piv], a[col]
        f = a[col][col]
        a[col] = [v / f for v in a[col]]
        for r in range(4):
            if r != col and a[r][col] != 0:
                g = a[r][col]
                a[r] = [v - g * w for v, w in zip(a[r], a[col])]
    return [row[4:] for row in a]


def rand_gauge(rng):
    """signed permutation times dyadic diagonal: invertible, sparse,
    keeps coefficients dyadic"""
    perm = list(range(4))
    rng.shuffle(perm)
    m = [[Fraction(0)] * 4 for _ in range(4)]
    for i, p in enumerate(perm):
        s = rng.choice([1, -1])
        e = rng.choice([Fraction(1, 2), Fraction(1), Fraction(1), Fraction(2)])
        m[i][p] = s * e
    return m


def sandwich_rows(rows, left, rightinv):
    """rows: 48 x 16 (vec of 4x4, row-major) -> left * M * rightinv"""
    out = []
    for r in rows:
        m = [[r[4 * i + j] for j in range(4)] for i in range(4)]
        m2 = mat4_mul(mat4_mul(left, m), rightinv)
        out.append([m2[i][j] for i in range(4) for j in range(4)])
    return out


def main():
    src, outdir, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rng = random.Random(seed)
    L = parse_sms(os.path.join(src, "L.sms"))
    R = parse_sms(os.path.join(src, "R.sms"))
    Pt = parse_sms(os.path.join(src, "P.sms"))  # 16 x 48
    C = [list(col) for col in zip(*Pt)]         # 48 x 16 (c~ rows)
    os.makedirs(outdir, exist_ok=True)
    made = 0
    tries = 0
    while made < n and tries < 20 * n:
        tries += 1
        gp, gq, gr = rand_gauge(rng), rand_gauge(rng), rand_gauge(rng)
        qi, ri = mat4_inv(gq), mat4_inv(gr)
        # correct action in this index convention (c is (i,j)-shaped):
        # a' = P a Q^-1, b' = Q b R^-1, c' = P^-T c R^T
        pit = [list(r) for r in zip(*mat4_inv(gp))]
        rt = [list(r) for r in zip(*gr)]
        L2 = sandwich_rows(L, gp, qi)
        R2 = sandwich_rows(R, gq, ri)
        P2 = [list(col) for col in zip(*sandwich_rows(C, pit, rt))]
        if not brent_ok(L2, R2, P2):
            continue
        L3, R3, P3 = primitive_gauge(L2, R2, P2)
        if not brent_ok(L3, R3, P3):
            continue
        d = os.path.join(outdir, f"sw{seed:02d}_{made:03d}")
        os.makedirs(d, exist_ok=True)
        write_sms(os.path.join(d, "L.sms"), L3)
        write_sms(os.path.join(d, "R.sms"), R3)
        write_sms(os.path.join(d, "P.sms"), P3)
        made += 1
    print(f"{made} sandwich variants written to {outdir} ({tries} tries)")


if __name__ == "__main__":
    main()
