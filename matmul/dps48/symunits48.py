#!/usr/bin/env python3
"""Which rows can be unit vectors at the symmetric points of a <4x4x4:48> class: the cross-leg
and mixed-element checks behind A. Sedoglavic's 'perfect situation'.

At a point h.T, h = (B_X^-1, B_Y^-1, B_Z^-1), where an order-4 stabilizer element g = (X, Y, Z)
acts by signed permutation matrices, each B is a basis adapted to its matrix.  In the cyclic
reading of lwh_transport a product with rank-1 factors U = u v^T, V = r s^T, W = p q^T becomes
U' = (B_X^-1 u)(B_Y^T v)^T, V' = (B_Y^-1 r)(B_Z^T s)^T, W' = (B_Z^-1 p)(B_X^T q)^T, so its L row
is a unit vector up to scale iff B_X^-1 u and B_Y^T v are (u 'primal' on B_X, v 'dual' on B_Y);
its R row: r primal on B_Y, s dual on B_Z; its P column: p primal on B_Z, q dual on B_X.  At such
a point a unit row spreads over the product's orbit under g, so unit rows come in orbits of
four, and a product with a rank-2 factor never has one.

Adapted bases: a matrix of char poly x^4 - 1 is conjugate to two signed permutations, the 4-cycle
C (B = [w, Mw, M^2 w, M^3 w]) and 1 + (-1) + J (B = [f+, f-, w, Mw], f+- eigenvectors for +-1,
w in ker(M^2 + I)); one of char poly (x -+ 1)^2 (x^2 + 1) only to 1 + 1 + J (B = [f1, f2, w, Mw],
f in ker(M - I)).  A set of requirements (leg, orbit) gives each slot primal and dual vectors;
it is achievable iff every slot has an adapted basis of an admissible form meeting all of them
(the slots are independent).  Decided exactly: a 4-cycle basis is fixed up to scale and column
shift by one primal vector, or by one dual vector through three linear equations; in the block
forms each column ranges over a subspace cut by linear conditions, and infeasibility is an empty
subspace, a forced violation of a nonvanishing condition, or forced dependence.  Every feasible
maximal set is confirmed by building the point and counting its unit rows.

Floors: no two products of the class share a factor up to scale (flip-isolated, an isotropy
invariant), so floor = 176 - (#rows exactly +-unit) >= 176 - (#rows unit up to scale); if at most
M orbits can be unit at once, every symmetric point has floor >= 176 - 4M.

  symunits48.py PREFIX
"""
import itertools
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lwh_family as F  # noqa: E402
import lwh_transport as LT  # noqa: E402
import slp48check as C  # noqa: E402
import symmetric48 as SY  # noqa: E402

mm, inv, TR = LT.mm, LT.inv, LT.T
I4 = SY.I4
UNDECIDED = []  # cases a generic choice could not settle (should stay empty)


def matvec(M, v):
    return [sum(M[i][j] * v[j] for j in range(4)) for i in range(4)]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def one_nonzero(v):
    return sum(1 for x in v if x != 0) == 1


def rank(vs):
    if not vs:
        return 0
    m = [list(v) for v in vs]
    r = 0
    for c in range(len(m[0])):
        p = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        r += 1
    return r


def in_span(x, basis):
    return rank(basis + [x]) == rank(basis)


def ker(M):
    return LT.nullspace([list(r) for r in M], 4)


def shifted(M, c):
    return [[M[i][j] - (c if i == j else 0) for j in range(4)] for i in range(4)]


def cut(basis, ys):
    """the subspace of span(basis) orthogonal to every y"""
    if not basis:
        return []
    rows = [[dot(y, b) for b in basis] for y in ys]
    if not rows:
        return basis
    coefs = LT.nullspace(rows, len(basis))
    return [[sum(c[k] * basis[k][i] for k in range(len(basis))) for i in range(4)] for c in coefs]


def generic(basis, nonzero_ys, avoid=()):
    """an element of span(basis) with y . v != 0 for each y and independent of every vector in
    avoid; None if impossible.  Forced failures are detected exactly; otherwise small
    combinations are tried (a failure there is recorded as undecided)."""
    if not basis:
        return None
    for y in nonzero_ys:
        if all(dot(y, b) == 0 for b in basis):
            return None  # forced: y is orthogonal to the whole subspace
    if len(basis) == 1:
        v = basis[0]
        ok = all(dot(y, v) != 0 for y in nonzero_ys) and all(rank([a, v]) == 2 for a in avoid)
        return v if ok else None
    for coefs in itertools.product(range(-3, 4), repeat=len(basis)):
        if not any(coefs):
            continue
        v = [sum(c * b[i] for c, b in zip(coefs, basis)) for i in range(4)]
        if all(dot(y, v) != 0 for y in nonzero_ys) and all(rank([a, v]) == 2 for a in avoid):
            return v
    UNDECIDED.append((len(basis), len(nonzero_ys), len(avoid)))
    return None


def cyclic_basis(M, w):
    vs = [w]
    for _ in range(3):
        vs.append(matvec(M, vs[-1]))
    return [[vs[j][i] for j in range(4)] for i in range(4)]


def checks(B, prims, duals):
    if SY.det(B) == 0:
        return False
    Bi, Bt = inv(B), TR(B)
    return all(one_nonzero(matvec(Bi, x)) for x in prims) and all(one_nonzero(matvec(Bt, y)) for y in duals)


def feas_cycle(M, prims, duals):
    """a basis with B^-1 M B = C meeting the requirements, or None"""
    if prims:
        B = cyclic_basis(M, prims[0])  # WLOG: scale and a column shift of B change nothing
        return B if checks(B, prims, duals) else None
    if duals:
        y0 = duals[0]
        MT = TR(M)
        rows, z = [], list(y0)
        for _ in range(3):
            z = matvec(MT, z)
            rows.append(list(z))  # y0^T M^j w = 0 for j = 1, 2, 3 (WLOG b = 0)
        sol = LT.nullspace(rows, 4)
        cands = [sol[0]] if len(sol) == 1 else []
        if len(sol) > 1:
            for coefs in itertools.product(range(-3, 4), repeat=len(sol)):
                if any(coefs):
                    cands.append([sum(c * b[i] for c, b in zip(coefs, sol)) for i in range(4)])
        for w in cands:
            B = cyclic_basis(M, w)
            if checks(B, [], duals):
                return B
        if len(sol) > 1:
            UNDECIDED.append(("cycle-dual", len(sol)))
        return None
    for coefs in itertools.product(range(-1, 2), repeat=4):
        if any(coefs):
            B = cyclic_basis(M, [Fr(c) for c in coefs])
            if SY.det(B) != 0:
                return B
    return None


def feas_block(M, form, prims, duals):
    """a basis [E+ columns, E- columns, w, Mw] (form 'S': 2 + 0, 'D1': 1 + 1) meeting the
    requirements, or None"""
    Ep, Em, Sw = ker(shifted(M, 1)), ker(shifted(M, -1)), ker([list(r) for r in
                                                               [[sum(M[i][k] * M[k][j] for k in range(4)) + (1 if i == j else 0)
                                                                 for j in range(4)] for i in range(4)]])
    dp, dm = (2, 0) if form == "S" else (1, 1)
    if (len(Ep), len(Em), len(Sw)) != (dp, dm, 2):
        return None
    colsE = [("+", i) for i in range(dp)] + [("-", i) for i in range(dm)]
    block = {"+": Ep, "-": Em}
    Minv = inv(M)
    MT = TR(M)
    popts = []
    for x in prims:
        o = [c for c in colsE if in_span(x, block[c[0]])]
        if in_span(x, Sw):
            o += [("w",), ("Mw",)]
        if not o:
            return None
        popts.append(o)
    dopts = []
    for y in duals:
        o = []
        for c in colsE:
            others = [b for k, bl in block.items() if k != c[0] for b in bl] + Sw
            if all(dot(y, b) == 0 for b in others):
                o.append(c)
        if all(dot(y, b) == 0 for b in Ep + Em):
            o += [("w",), ("Mw",)]
        if not o:
            return None
        dopts.append(o)
    for pa in itertools.product(*popts):
        for da in itertools.product(*dopts):
            # each eigen-column: its subspace (the block, or the line of its primal vector, cut by
            # the duals assigned to other columns of the block) and its nonvanishing duals
            spec, ok = {}, True
            for c in colsE:
                basis = block[c[0]]
                xs = [x for x, a in zip(prims, pa) if a == c]
                if xs:
                    if rank(xs) > 1:
                        ok = False
                        break
                    basis = [xs[0]]
                perp = [y for y, a in zip(duals, da) if a != c and a[0] == c[0]]
                spec[c] = (cut(basis, perp), [y for y, a in zip(duals, da) if a == c])
            if not ok:
                continue
            cols = {}
            for c in sorted(colsE, key=lambda c: len(spec[c][0])):  # forced columns first
                v = generic(spec[c][0], spec[c][1], avoid=[cols[d] for d in cols if d[0] == c[0]])
                if v is None:
                    ok = False
                    break
                cols[c] = v
            if not ok:
                continue
            # the swap pair (w, Mw): w in ker(M^2 + I), on the line of a primal vector if one is
            # assigned (x at w, or M^-1 x at Mw), orthogonal to M^T y for a dual y at w (y . Mw = 0)
            # and to y for a dual at Mw (y . w = 0)
            basis = Sw
            tgt = [x if a == ("w",) else matvec(Minv, x) for x, a in zip(prims, pa) if a in (("w",), ("Mw",))]
            if tgt:
                if rank(tgt) > 1:
                    continue
                basis = [tgt[0]]
            perp = [matvec(MT, y) for y, a in zip(duals, da) if a == ("w",)]
            perp += [y for y, a in zip(duals, da) if a == ("Mw",)]
            basis = cut(basis, perp)
            nz = [y for y, a in zip(duals, da) if a == ("w",)]
            nz += [matvec(MT, y) for y, a in zip(duals, da) if a == ("Mw",)]
            w = generic(basis, nz)
            if w is None:
                continue
            B = [[cols[c][i] for c in colsE] + [w[i], matvec(M, w)[i]] for i in range(4)]
            if checks(B, prims, duals):
                return B
    return None


def charpoly(M):
    return SY.charpoly(M)


def forms(M):
    """(normalized M, admissible forms) for an order-4 factor"""
    cp = charpoly(M)
    if cp == SY.CP_FIXNEG:
        M = [[-x for x in row] for row in M]
        cp = SY.CP_FIX
    if cp == SY.CP_CYC:
        return M, ["C", "D1"]
    if cp == SY.CP_FIX:
        return M, ["S"]
    raise ValueError(f"unexpected char poly {cp}")


def slot_basis(M, fms, prims, duals):
    for f in fms:
        B = feas_cycle(M, prims, duals) if f == "C" else feas_block(M, f, prims, duals)
        if B is not None:
            return f, B
    return None


LEGS = {"L": ((0, "u", "prim"), (1, "v", "dual")),
        "R": ((1, "r", "prim"), (2, "s", "dual")),
        "P": ((2, "p", "prim"), (0, "q", "dual"))}


def feasible(reqs, Ms, fms, vecs):
    per = [([], []) for _ in range(3)]
    for leg, o in reqs:
        for slot, name, kind in LEGS[leg]:
            per[slot][0 if kind == "prim" else 1].append(vecs[o][name])
    out = []
    for slot in range(3):
        sb = slot_basis(Ms[slot], fms[slot], *per[slot])
        if sb is None:
            return None
        out.append(sb)
    return out


def unit_rows(T1):
    L, R, P = F.to_lrp(*T1, True)
    cnt = lambda rows: sum(1 for r in rows if sum(1 for x in r if x != 0) == 1)
    return cnt(L), cnt(R), cnt([list(c) for c in zip(*P)])


def main():
    prefix = sys.argv[1]
    U, V, W = F.read_lrp(prefix)
    T = (U, V, [TR(M) for M in W])
    assert C.brent(*F.to_lrp(*T, True)) == 0
    elems = SY.order4_elements(T)
    print(f"{os.path.basename(prefix)}: {len(elems)} order-4 elements with trivial slot map")
    overall = 0
    for k, ((X, Y, Z), pi) in enumerate(elems):
        norm = [forms(M) for M in (X, Y, Z)]
        Ms, fms = [n[0] for n in norm], [n[1] for n in norm]
        orbs = [o for o in SY.orbits(pi) if F.rank(U[o[0]]) == 1]
        vecs = []
        for o in orbs:
            kk = o[0]
            vecs.append({"u": LT.colvec(U[kk]), "v": SY.rowvec(U[kk]), "r": LT.colvec(V[kk]),
                         "s": SY.rowvec(V[kk]), "p": LT.colvec(T[2][kk]), "q": SY.rowvec(T[2][kk])})
        reqs = [(leg, i) for leg in "LRP" for i in range(len(orbs))]
        level = [frozenset([r]) for r in reqs if feasible([r], Ms, fms, vecs)]
        singles = {leg: sum(1 for s in level if next(iter(s))[0] == leg) for leg in "LRP"}
        best, sets = level, level
        while sets:
            prev = set(sets)
            nxt = set()
            for s in sets:
                top = max(reqs.index(r) for r in s)
                for r in reqs[top + 1:]:
                    t = s | {r}
                    if t not in nxt and all((t - {q}) in prev for q in t) and feasible(sorted(t), Ms, fms, vecs):
                        nxt.add(t)
            if nxt:
                best = list(nxt)
            sets = list(nxt)
        msize = max((len(s) for s in best), default=0)
        cross = any(len({r[0] for r in s}) > 1 for s in best)
        legs_used = sorted({r[0] for s in best for r in s})
        # confirm one maximal set by building the point
        ex = sorted(best[0]) if best else []
        conf = ""
        if ex:
            bs = feasible(ex, Ms, fms, vecs)
            T1 = SY.sandwich(T, *(inv(b[1]) for b in bs))
            assert C.brent(*F.to_lrp(*T1, True)) == 0
            assert SY.is_signed_perm_stab(T1, None, pi), "the element is not a signed permutation there"
            ul = unit_rows(T1)
            conf = f"; built: forms {'/'.join(b[0] for b in bs)}, unit-up-to-scale rows L/R/P {ul}"
            want = [4 * sum(1 for r in ex if r[0] == leg) for leg in "LRP"]
            assert all(g >= w for g, w in zip(ul, want)), (ul, want)
        overall = max(overall, msize)
        kinds = "/".join("cyc" if f == ["C", "D1"] else "fix2swap" for f in fms)
        print(f"  element {k:2d} {kinds:22s} unit orbits feasible alone L/R/P {singles['L']}/{singles['R']}/{singles['P']}; "
              f"at most {msize} at once (legs {''.join(legs_used)}{', across legs' if cross else ', one leg'}) "
              f"-> floor >= {176 - 4 * msize}{conf}", flush=True)
    print(f"every symmetric point (any of the {len(elems)} elements): at most {overall} unit orbits, "
          f"floor >= {176 - 4 * overall}; undecided generic choices: {len(UNDECIDED)}")


if __name__ == "__main__":
    main()
