#!/usr/bin/env python3
"""Transport a sparse representative of the DPS class along the Li-Wang-Hu family.

The DPS class is the member s(1/4) of the Li-Wang-Hu curve s(t) (invariant phi = 192).
This script finds an explicit isotropy g with g . s(1/4) = TARGET (a sparse point of the
DPS class, e.g. our 201 point) and writes g . s(t) for other t: representatives of the
other classes in the same coordinates as TARGET.  In the cyclic convention used here
(sum_k U_k (x) V_k (x) W_k = sum e_ij (x) e_jl (x) e_li) the isotropies are
  (U, V, W) -> (X U Y^-1, Y V Z^-1, Z W X^-1), per-layer scalings (a U, b V, W/(ab)),
  layer permutations, and S3: (U,V,W) -> (V,W,U) and (U,V,W) -> (W^T, V^T, U^T).
Layers are matched by isotropy invariants (factor rank triples and the ranks of side-by-
side and stacked factor pairs, refined Weisfeiler-Leman style, then backtracking); X, Y, Z
are solved exactly from the rank-one layers (X u ~ u', Y r ~ r', Z p ~ p' for the column
vectors of the U, V, W factors) and the whole map is checked layer by layer.

  lwh_transport.py TEX TARGETPREFIX OUTDIR T [T ...]
writes OUTDIR/tr_<T>_{L,R,P}.sms for each t (Brent-checked), in our convention.
"""
import itertools
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lwh_family as F  # noqa: E402
import slp48check as C  # noqa: E402


def T(M):
    return [[M[j][i] for j in range(4)] for i in range(4)]


def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def inv(M):
    n = len(M)
    A = [row[:] + [Fr(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        piv = A[c][c]
        A[c] = [x / piv for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [row[n:] for row in A]


def s3_variants(D):
    U, V, W = D
    Tl = lambda L: [T(M) for M in L]  # noqa: E731
    base = [("id", (U, V, W)), ("cyc", (V, W, U)), ("cyc2", (W, U, V))]
    out = []
    for name, (a, b, c) in base:
        out.append((name, (a, b, c)))
        out.append((name + "+rev", (Tl(c), Tl(b), Tl(a))))
    return out


# ------------------------------------------------------------------ invariants
def colors(D):
    U, V, W = D
    n = len(U)
    vc = [(F.rank(U[k]), F.rank(V[k]), F.rank(W[k])) for k in range(n)]
    pc = {}
    for i in range(n):
        for j in range(i + 1, n):
            key = []
            for Fa in (U, V, W):
                side = [Fa[i][r] + Fa[j][r] for r in range(4)]          # 4x8 [A_i A_j]
                stack = Fa[i] + Fa[j]                                     # 8x4 [A_i; A_j]
                key += [F.rank(side), F.rank(stack)]
            pc[(i, j)] = pc[(j, i)] = tuple(key)
    return vc, pc


def refine(vcS, pcS, vcT, pcT, n, rounds=6):
    cS, cT = [hash(("v", c)) for c in vcS], [hash(("v", c)) for c in vcT]
    for _ in range(rounds):
        nS = [hash((cS[i], tuple(sorted((pcS[(i, j)], cS[j]) for j in range(n) if j != i)))) for i in range(n)]
        nT = [hash((cT[i], tuple(sorted((pcT[(i, j)], cT[j]) for j in range(n) if j != i)))) for i in range(n)]
        cS, cT = nS, nT
    return cS, cT


def isomorphisms(vcS, pcS, vcT, pcT):
    n = len(vcS)
    cS, cT = refine(vcS, pcS, vcT, pcT, n)
    if sorted(cS) != sorted(cT):
        return
    order = sorted(range(n), key=lambda i: (sum(1 for c in cS if c == cS[i]), i))
    pi, used = {}, set()

    def bt(d):
        if d == n:
            yield dict(pi)
            return
        i = order[d]
        for j in range(n):
            if j in used or cT[j] != cS[i]:
                continue
            if all(pcS[(i, k)] == pcT[(j, pi[k])] for k in pi):
                pi[i] = j
                used.add(j)
                yield from bt(d + 1)
                del pi[i]
                used.discard(j)

    yield from bt(0)


# ------------------------------------------------------------------ solving X, Y, Z
def nullspace(rows, ncols):
    A = [r[:] for r in rows]
    piv_cols, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv_cols.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv_cols]
    basis = []
    for fc in free:
        v = [Fr(0)] * ncols
        v[fc] = Fr(1)
        for row_i, pc in enumerate(piv_cols):
            v[pc] = -A[row_i][fc]
        basis.append(v)
    return basis


def solve_map(pairs):
    """M (4x4) with M x_k ~ y_k for all pairs (x_k, y_k); None unless unique up to scale."""
    n = len(pairs)
    rows = []
    for k, (x, y) in enumerate(pairs):
        for i in range(4):
            row = [Fr(0)] * (16 + n)
            for j in range(4):
                row[4 * i + j] = x[j]
            row[16 + k] = -y[i]
            rows.append(row)
    ns = nullspace(rows, 16 + n)
    if len(ns) != 1:
        return None
    v = ns[0]
    M = [[v[4 * i + j] for j in range(4)] for i in range(4)]
    if F.rank(M) < 4:
        return None
    return M


def colvec(M):
    """a nonzero column of a rank-1 matrix."""
    for j in range(4):
        col = [M[i][j] for i in range(4)]
        if any(col):
            return col
    raise ValueError("zero matrix")


def ratio(A, B):
    """scalar s with A = s B, or None."""
    s = None
    for i in range(4):
        for j in range(4):
            if B[i][j] == 0:
                if A[i][j] != 0:
                    return None
                continue
            r = A[i][j] / B[i][j]
            if s is None:
                s = r
            elif r != s:
                return None
    return s


def try_transport(S, Tg, pi):
    U, V, W = S
    U2, V2, W2 = Tg
    r1 = [k for k in range(48) if F.rank(U[k]) == 1]
    X = solve_map([(colvec(U[k]), colvec(U2[pi[k]])) for k in r1])
    Y = solve_map([(colvec(V[k]), colvec(V2[pi[k]])) for k in r1])
    Z = solve_map([(colvec(W[k]), colvec(W2[pi[k]])) for k in r1])
    if X is None or Y is None or Z is None:
        return None
    Xi, Yi, Zi = inv(X), inv(Y), inv(Z)
    a, b = [None] * 48, [None] * 48
    for k in range(48):
        a[k] = ratio(U2[pi[k]], mm(mm(X, U[k]), Yi))
        b[k] = ratio(V2[pi[k]], mm(mm(Y, V[k]), Zi))
        if a[k] is None or b[k] is None or a[k] == 0 or b[k] == 0:
            return None
        Wt = mm(mm(Z, W[k]), Xi)
        if ratio(W2[pi[k]], Wt) != 1 / (a[k] * b[k]):
            return None
    return X, Y, Z, Xi, Yi, Zi, a, b


def apply(g, S, pi):
    X, Y, Z, Xi, Yi, Zi, a, b = g
    U, V, W = S
    out = ([None] * 48, [None] * 48, [None] * 48)
    for k in range(48):
        out[0][pi[k]] = [[a[k] * x for x in row] for row in mm(mm(X, U[k]), Yi)]
        out[1][pi[k]] = [[b[k] * x for x in row] for row in mm(mm(Y, V[k]), Zi)]
        out[2][pi[k]] = [[x / (a[k] * b[k]) for x in row] for row in mm(mm(Z, W[k]), Xi)]
    return out


def main():
    tex, target, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
    ts = [Fr(x) for x in sys.argv[4:]]
    os.makedirs(outdir, exist_ok=True)
    layers = F.parse(tex)
    tw = F.find_convention(layers)
    assert tw, "expected the cyclic convention (output factor transposed)"
    # target in the cyclic convention: W = (column of P)^T
    Ut, Vt, Wt = F.read_lrp(target)
    Tg = (Ut, Vt, [T(M) for M in Wt])
    assert C.brent(*F.to_lrp(*Tg, True)) == 0, "target fails Brent in the cyclic reading"
    vcT, pcT = colors(Tg)
    S0 = F.scheme(layers, Fr(1, 4))
    found = None
    for name, S in s3_variants(S0):
        vcS, pcS = colors(S)
        tried = 0
        for pi in isomorphisms(vcS, pcS, vcT, pcT):
            tried += 1
            g = try_transport(S, Tg, pi)
            if g is not None:
                found = (name, pi, g)
                break
            if tried >= 2000:
                break
        print(f"S3 variant {name}: {'TRANSPORT FOUND' if found else 'no transport'} after {tried} matchings", flush=True)
        if found:
            break
    assert found, "no isotropy found"
    name, pi, g = found
    # check: g . s(1/4) == target exactly
    img = apply(g, dict(s3_variants(S0))[name], pi)
    assert img == [list(Tg[0]), list(Tg[1]), list(Tg[2])] or all(img[f][k] == Tg[f][k] for f in range(3) for k in range(48)), "image differs from target"
    print(f"isotropy: S3 {name}, X = {g[0]}, Y = {g[1]}, Z = {g[2]}")
    for t in ts:
        S = dict(s3_variants(F.scheme(layers, t)))[name]
        Ui, Vi, Wi = apply(g, S, pi)
        L, R, P = F.to_lrp(Ui, Vi, Wi, True)
        assert C.brent(L, R, P) == 0, f"transported s({t}) fails Brent"
        tag = str(t).replace("/", "o")
        for nm, M in (("L", L), ("R", R), ("P", P)):
            F.write_sms(os.path.join(outdir, f"tr_{tag}_{nm}.sms"), M)
        same_L = sum(L[k] == F.C_read(target + "_L.sms")[k] for k in range(48))
        vals = sorted({abs(x) for M in (L, R, P) for row in M for x in row if x})
        ph, _, _ = F.phi(Ui, Vi, Wi)
        print(f"  t = {t}: Brent 4096/4096, phi {ph} ({'matches' if ph == 64 + 4 / (t * t) + 1024 * t * t else 'MISMATCH'}), "
              f"L rows equal to the target's {same_L}/48, |coefficients| {[str(v) for v in vals]}", flush=True)


if __name__ == "__main__":
    main()
