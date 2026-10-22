#!/usr/bin/env python3
"""Agarwal's twelve-term replacement of the Li-Wang-Hu scheme s(2) (arXiv:2609.13596,
Proposition "An exact twelve-term replacement", Appendix "A sharp strong radius").

The construction is rebuilt here from its statement, in exact rational arithmetic, from
the family as parsed by lwh_family.py (Agarwal's D(t) is the Li-Wang-Hu family with the
paper's stored matrices, layers numbered 1..48).  Groups (1-based layers):
  F = (9, 25, 28, 35), G = (12, 19, 22, 32), U = (4, 17, 34, 40).
Modes 1 and 2 use the factors of F then G as an ordered basis (rank 8), mode 3 those of
G then U.  With coordinates in these bases, the twelve layers F, G, U are replaced by
  (e_f, e_f + lambda_f (0, bbar_{j_f}), (c_f, 0))      f = 1..4
  ((0, a'_j), (0, b'_j), (c'_j, 0))                    j = 1..4
  (a_j, b_j, (-r_j, e_j))                              j = 1..4
with R, A', B', C' = B'/2, j_f = (3, 1, 4, 2), lambda_f = (3, -3, -3/4, -3) as given.
The result is checked on all 4096 Brent equations, its new factor rank triples are
compared with the paper's (2,3,2), (2,3,3), (2,2,3) four each, and it is written as a
PLinOpt sms triple in our convention.

  agarwal_replacement.py TEX OUTPREFIX
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lwh_family as F  # noqa: E402
import slp48check as C  # noqa: E402

FG = (9, 25, 28, 35)
GG = (12, 19, 22, 32)
UG = (4, 17, 34, 40)


def flat(M):
    return [M[i][j] for i in range(4) for j in range(4)]


def unflat(v):
    return [[v[4 * i + j] for j in range(4)] for i in range(4)]


def solve(cols, x):
    """exact coordinates c with sum_k c_k cols[k] = x (cols independent); error if x is
    not in their span."""
    n, m = len(x), len(cols)
    A = [[cols[k][i] for k in range(m)] + [x[i]] for i in range(n)]
    piv, r = [], 0
    for c in range(m):
        p = next((i for i in range(r, n) if A[i][c] != 0), None)
        assert p is not None, "basis is rank deficient"
        A[r], A[p] = A[p], A[r]
        inv = 1 / A[r][c]
        A[r] = [a * inv for a in A[r]]
        for i in range(n):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    for i in range(r, n):
        assert A[i][m] == 0, "vector not in the span of the basis"
    return [A[k][m] for k in range(m)]


def combo(cols, c):
    return [sum(c[k] * cols[k][i] for k in range(len(cols))) for i in range(len(cols[0]))]


def mat(rows, scale):
    return [[Fr(x) * scale for x in row] for row in rows]


def column(M, j):
    return [M[i][j] for i in range(len(M))]


def build(tex):
    layers = F.parse(tex)
    U, V, W = F.scheme(layers, Fr(2))  # Li-Wang-Hu convention, W as given
    L = lambda grp, fac: [flat(fac[k - 1]) for k in grp]  # noqa: E731
    B1 = L(FG, U) + L(GG, U)   # mode-1 basis: first factors of F then G
    B2 = L(FG, V) + L(GG, V)   # mode-2 basis
    B3 = L(GG, W) + L(UG, W)   # mode-3 basis: third factors of G then U
    # coordinates
    c = [solve(B3, flat(W[k - 1]))[:4] for k in FG]                 # c_f (G-part)
    a = [solve(B1, flat(U[k - 1])) for k in UG]                      # a_j (8 coords)
    b = [solve(B2, flat(V[k - 1])) for k in UG]                      # b_j
    e3 = [solve(B3, flat(W[k - 1])) for k in UG]
    for j in range(4):
        assert e3[j] == [0] * 4 + [1 if i == j else 0 for i in range(4)], "third factor of U_j is not (0, e_j)"
        assert all(x == 0 for x in b[j][:4]), "b_j does not have zero top part"
    abar = [aj[4:] for aj in a]
    bbar = [bj[4:] for bj in b]
    R = mat([[12, 12, 12, -3], [12, -12, 12, 3], [12, 12, -12, 3], [-12, 12, 12, 3]], Fr(1, 8))
    Ap = mat([[9, -3, -3, 1], [-3, 9, 1, -3], [-3, 1, 9, -3], [1, -3, -3, 9]], Fr(1, 8))
    Bp = mat([[3, 0, 0, 1], [0, 3, -1, 0], [0, -1, 3, 0], [1, 0, 0, 3]], Fr(1, 2))
    Cp = [[x / 2 for x in row] for row in Bp]
    r = [column(R, j) for j in range(4)]
    ap = [column(Ap, j) for j in range(4)]
    bp = [column(Bp, j) for j in range(4)]
    cp = [column(Cp, j) for j in range(4)]
    jf = [3, 1, 4, 2]
    lam = [Fr(3), Fr(-3), Fr(-3, 4), Fr(-3)]
    e = lambda i, n=4: [Fr(1) if k == i else Fr(0) for k in range(n)]  # noqa: E731
    # the paper's two consistency facts
    for f in range(4):
        j = jf[f] - 1
        assert r[j] == [lam[f] * x for x in c[f]], f"r_(j_{f + 1}) != lambda_f c_f"
        assert a[j][:4] == e(f), f"top of a_(j_{f + 1}) is not e_{f + 1}"
    # the displayed 4-dimensional identity
    lhs = {}
    for s in range(4):
        lhs[(s, s, s)] = lhs.get((s, s, s), 0) + 1
    for j in range(4):
        for x in range(4):
            for y in range(4):
                for z in range(4):
                    v = abar[j][x] * bbar[j][y] * r[j][z]
                    if v:
                        lhs[(x, y, z)] = lhs.get((x, y, z), 0) + v
    rhs = {}
    for j in range(4):
        for x in range(4):
            for y in range(4):
                for z in range(4):
                    v = ap[j][x] * bp[j][y] * cp[j][z]
                    if v:
                        rhs[(x, y, z)] = rhs.get((x, y, z), 0) + v
    keys = set(lhs) | set(rhs)
    assert all(lhs.get(k, 0) == rhs.get(k, 0) for k in keys), "displayed identity fails"
    # the twelve new triples, in basis coordinates, mapped back to 16 dimensions
    new = []
    for f in range(4):
        j = jf[f] - 1
        x1 = e(f, 8)
        x2 = [e(f, 8)[k] + (lam[f] * bbar[j][k - 4] if k >= 4 else 0) for k in range(8)]
        x3 = c[f] + [Fr(0)] * 4
        new.append((x1, x2, x3))
    for j in range(4):
        new.append(([Fr(0)] * 4 + ap[j], [Fr(0)] * 4 + bp[j], cp[j] + [Fr(0)] * 4))
    for j in range(4):
        new.append((a[j], b[j], [-x for x in r[j]] + e(j)))
    newU = [unflat(combo(B1, t[0])) for t in new]
    newV = [unflat(combo(B2, t[1])) for t in new]
    newW = [unflat(combo(B3, t[2])) for t in new]
    removed = set(FG) | set(GG) | set(UG)
    keep = [k for k in range(1, 49) if k not in removed]
    U2 = [U[k - 1] for k in keep] + newU
    V2 = [V[k - 1] for k in keep] + newV
    W2 = [W[k - 1] for k in keep] + newW
    return (U, V, W), (U2, V2, W2), (newU, newV, newW), layers


def main():
    tex, out = sys.argv[1], sys.argv[2]
    (U, V, W), (U2, V2, W2), (nU, nV, nW), layers = build(tex)
    tw = F.find_convention(layers)
    Lm, Rm, Pm = F.to_lrp(U2, V2, W2, tw)
    bad = C.brent(Lm, Rm, Pm)
    print(f"replacement scheme: {4096 - bad}/4096 Brent equations hold")
    assert bad == 0
    trip = {}
    for k in range(12):
        tr = (F.rank(nU[k]), F.rank(nV[k]), F.rank(nW[k]))
        trip[tr] = trip.get(tr, 0) + 1
    print(f"new factor rank triples: {trip}  (paper: (2,3,2) x4, (2,3,3) x4, (2,2,3) x4)")
    olds = {(tuple(flat(U[k])), tuple(flat(V[k])), tuple(flat(W[k]))) for k in range(48)}
    clash = sum((tuple(flat(nU[k])), tuple(flat(nV[k])), tuple(flat(nW[k]))) in olds for k in range(12))
    print(f"new triples equal to an original triple: {clash} (paper: none)")
    for name, M in (("L", Lm), ("R", Rm), ("P", Pm)):
        F.write_sms(f"{out}_{name}.sms", M)
    vals = sorted({abs(x) for M in (Lm, Rm, Pm) for row in M for x in row if x})
    print(f"wrote {out}_{{L,R,P}}.sms; |coefficients| {[str(v) for v in vals]}")


if __name__ == "__main__":
    main()
