#!/usr/bin/env python3
"""3x3 starting points for the rational flip graph (A. Sedoglavic's item 6).

std27: the classical <3x3x3:27>, one product A[a,b] B[b,c] per output term.
gm25:  Grochow and Moore's <3x3x3:25> (arXiv:1612.01527, Section 5, Eq. (36), n = 3):
       MM = 1 (x) 1 (x) 1 + (n/(n+1))^3 sum over distinct (i, j, k) of
            |w_i><w_j - w_i| (x) |w_j><w_k - w_j| (x) |w_k><w_i - w_k|,
       w_1..w_4 the unit vectors to the corners of a simplex, here v_i / sqrt(3) with
       v = (-1,1,1), (1,-1,1), (1,1,-1), (-1,-1,-1); <MM | A (x) B (x) C> = tr(ABC).
       Each of the 24 terms is (1/64) v_i (v_j - v_i)^T (x) v_j (v_k - v_j)^T (x) v_k (v_i - v_k)^T.

A decomposition tr(ABC) = sum_r <X_r, A> <Y_r, B> <Z_r, C> gives AB = sum_r <X_r, A> <Y_r, B> Z_r^T,
so in our convention vec(AB) = P((L vecA) . (R vecB)) (row-major vec): L row r = vec X_r,
R row r = vec Y_r, P column r = vec Z_r^T.  Writes {std27,gm25}/{L,R,P}.sms next to this
script and checks all 729 Brent equations exactly.

  seeds.py
"""
import itertools
import os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))


def vec(M):
    return [M[r][c] for r in range(3) for c in range(3)]


def outer(u, v):
    return [[Fraction(u[r]) * v[c] for c in range(3)] for r in range(3)]


def transpose(M):
    return [[M[c][r] for c in range(3)] for r in range(3)]


def brent(L, R, P):
    """number of the 729 equations sum_r L[r,x] R[r,y] P[z,r] = T[x,y,z] that fail"""
    bad = 0
    for x, y, z in itertools.product(range(9), repeat=3):
        want = 1 if (x % 3 == y // 3 and x // 3 == z // 3 and y % 3 == z % 3) else 0
        if sum(L[r][x] * R[r][y] * P[z][r] for r in range(len(L))) != want:
            bad += 1
    return bad


def std27():
    E = lambda a, b: [[Fraction(int((r, c) == (a, b))) for c in range(3)] for r in range(3)]
    L, R, Pt = [], [], []
    for a, b, c in itertools.product(range(3), repeat=3):
        L.append(vec(E(a, b)))
        R.append(vec(E(b, c)))
        Pt.append(vec(E(a, c)))
    return L, R, [list(col) for col in zip(*Pt)]


def gm25():
    v = [(-1, 1, 1), (1, -1, 1), (1, 1, -1), (-1, -1, -1)]
    d = lambda p, q: [x - y for x, y in zip(v[p], v[q])]
    I = [[Fraction(int(r == c)) for c in range(3)] for r in range(3)]
    L, R, Pt = [vec(I)], [vec(I)], [vec(I)]
    for i, j, k in itertools.permutations(range(4), 3):
        X = outer(v[i], d(j, i))
        Y = outer(v[j], d(k, j))
        Z = outer(v[k], d(i, k))
        L.append(vec(X))
        R.append(vec(Y))
        Pt.append([Fraction(1, 64) * z for z in vec(transpose(Z))])
    return L, R, [list(col) for col in zip(*Pt)]


def fmt(q):
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def write_sms(path, M):
    with open(path, "w") as f:
        f.write(f"{len(M)} {len(M[0])} M\n")
        for i, row in enumerate(M):
            for j, q in enumerate(row):
                if q != 0:
                    assert q.denominator & (q.denominator - 1) == 0, "not dyadic"
                    f.write(f"{i + 1} {j + 1} {fmt(q)}\n")
        f.write("0 0 0\n")


def main():
    for name, build in (("std27", std27), ("gm25", gm25)):
        L, R, P = build()
        bad = brent(L, R, P)
        print(f"{name}: rank {len(L)}, {729 - bad}/729 Brent equations hold")
        assert bad == 0
        out = os.path.join(HERE, name)
        os.makedirs(out, exist_ok=True)
        for nm, M in (("L", L), ("R", R), ("P", P)):
            write_sms(os.path.join(out, f"{nm}.sms"), M)
        print(f"  wrote {out}/{{L,R,P}}.sms")


if __name__ == "__main__":
    main()
