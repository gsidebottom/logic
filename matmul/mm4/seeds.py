#!/usr/bin/env python3
"""4x4 starting points for the rational flip-graph descent (the type-bias test on 4x4).

std64:      the classical <4x4x4:64>, one product A[a,b] B[b,c] per output term.
strassen49: Strassen's 2x2 algorithm applied to 2x2 blocks of 2x2 blocks (<2,2,2> (x) <2,2,2>):
            the 49 Kronecker products of his 7 products, index (i1, i2) -> 2 i1 + i2.

Our convention: vec(AB) = P((L vecA) . (R vecB)) with row-major vec.  Writes
{std64,strassen49}/{L,R,P}.sms next to this script and checks all 4096 Brent equations exactly.

  seeds.py
"""
import itertools
import os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))

# Strassen: M1 = (A11 + A22)(B11 + B22), M2 = (A21 + A22) B11, M3 = A11 (B12 - B22),
# M4 = A22 (B21 - B11), M5 = (A11 + A12) B22, M6 = (A21 - A11)(B11 + B12), M7 = (A12 - A22)(B21 + B22);
# C11 = M1 + M4 - M5 + M7, C12 = M3 + M5, C21 = M2 + M4, C22 = M1 - M2 + M3 + M6.
# Rows of L and R and columns of P, each as the row-major 2x2 coefficient matrix.
S_L = [(1, 0, 0, 1), (0, 0, 1, 1), (1, 0, 0, 0), (0, 0, 0, 1), (1, 1, 0, 0), (-1, 0, 1, 0), (0, 1, 0, -1)]
S_R = [(1, 0, 0, 1), (1, 0, 0, 0), (0, 1, 0, -1), (-1, 0, 1, 0), (0, 0, 0, 1), (1, 1, 0, 0), (0, 0, 1, 1)]
S_P = [(1, 0, 0, 1), (0, 0, 1, -1), (0, 1, 0, 1), (1, 0, 1, 0), (-1, 1, 0, 0), (0, 0, 0, 1), (1, 0, 0, 0)]


def brent(L, R, P, n):
    """number of the n^6 equations sum_r L[r,x] R[r,y] P[z,r] = T[x,y,z] that fail"""
    N = n * n
    bad = 0
    for x, y, z in itertools.product(range(N), repeat=3):
        want = 1 if (x % n == y // n and x // n == z // n and y % n == z % n) else 0
        if sum(L[r][x] * R[r][y] * P[z][r] for r in range(len(L))) != want:
            bad += 1
    return bad


def std(n):
    E = lambda a, b: [Fraction(int(i == a * n + b)) for i in range(n * n)]
    L, R, Pt = [], [], []
    for a, b, c in itertools.product(range(n), repeat=3):
        L.append(E(a, b))
        R.append(E(b, c))
        Pt.append(E(a, c))
    return L, R, [list(col) for col in zip(*Pt)]


def kron2(u, v):
    """Kronecker product of two row-major 2x2 matrices as a row-major 4x4 matrix"""
    out = [Fraction(0)] * 16
    for i1, j1, i2, j2 in itertools.product(range(2), repeat=4):
        out[(2 * i1 + i2) * 4 + (2 * j1 + j2)] = Fraction(u[2 * i1 + j1] * v[2 * i2 + j2])
    return out


def strassen49():
    L, R, Pt = [], [], []
    for r, s in itertools.product(range(7), repeat=2):
        L.append(kron2(S_L[r], S_L[s]))
        R.append(kron2(S_R[r], S_R[s]))
        Pt.append(kron2(S_P[r], S_P[s]))
    return L, R, [list(col) for col in zip(*Pt)]


def write_sms(path, M):
    with open(path, "w") as f:
        f.write(f"{len(M)} {len(M[0])} M\n")
        for i, row in enumerate(M):
            for j, q in enumerate(row):
                if q != 0:
                    assert q.denominator == 1
                    f.write(f"{i + 1} {j + 1} {q.numerator}\n")
        f.write("0 0 0\n")


def main():
    for name, build in (("std64", lambda: std(4)), ("strassen49", strassen49)):
        L, R, P = build()
        bad = brent(L, R, P, 4)
        print(f"{name}: rank {len(L)}, {4096 - bad}/4096 Brent equations hold")
        assert bad == 0
        out = os.path.join(HERE, name)
        os.makedirs(out, exist_ok=True)
        for nm, M in (("L", L), ("R", R), ("P", P)):
            write_sms(os.path.join(out, f"{nm}.sms"), M)
        print(f"  wrote {out}/{{L,R,P}}.sms")


if __name__ == "__main__":
    main()
