#!/usr/bin/env python3
"""Points of a <4x4x4:48> class where an order-4 stabilizer element acts by signed permutation
matrices (A. Sedoglavic's 'perfect situation'), and the search for sparse ones among them.

Step 1 (build): each order-4 element g = (X, Y, Z) with trivial slot map of the stabilizer of
PREFIX is normalized so X^4 = Y^4 = Z^4 = I (up to the projective sign).  On lam01c0_201 each
matrix has char poly x^4 - 1 (a 4-cycle type) or (x -+ 1)^2 (x^2 + 1) (fixed-fixed-swap type;
the sign is the projective one, flipped to (x-1)^2 (x^2+1)).  Adapted bases from small integer
vectors, keeping only determinants +-2^k so the point stays over Z[1/2]: a cyclic vector v, Mv,
M^2 v, M^3 v for the 4-cycle type (target C, the 4-cycle permutation matrix); two fixed vectors,
then w and Mw with M^2 w = -w for the other (target S = 1 + 1 + [[0,-1],[1,0]], a signed
permutation).  With B the basis matrices, h = (B_X^-1, B_Y^-1, B_Z^-1) maps PREFIX to a point
where h g h^-1 is the target triple.  Cyclic reading of lwh_transport throughout:
(U, V, W) -> (X U Y^-1, Y V Z^-1, Z W X^-1).

Step 2 (search): the isotropies keeping the target triple are D = (D_X, D_Y, D_Z) with each
factor in the centralizer of its target: circulants (polynomials in C) with dyadic determinant
for C; A + (a I + b J) (A in GL(2), a + b i a unit of Z[i][1/2]) for S.  Metropolis over products
of generators of that group, objective as in orbit48: floor_L + floor_R + floor_Pt + 32 + lam *
(#coefficients not in {0, +-1}).

  symmetric48.py PREFIX OUTDIR [--steps N] [--restarts R] [--lam 0.1] [--seed S]
"""
import itertools
import math
import os
import random
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lwh_family as F  # noqa: E402
import lwh_transport as LT  # noqa: E402
import slp48check as C  # noqa: E402
import stabilizer48 as S48  # noqa: E402

mm, inv = LT.mm, LT.inv
I4 = [[Fr(int(i == j)) for j in range(4)] for i in range(4)]
J2 = [[Fr(0), Fr(-1)], [Fr(1), Fr(0)]]
S_X = [[Fr(1), 0, 0, 0], [0, Fr(1), 0, 0], [0, 0, 0, Fr(-1)], [0, 0, Fr(1), 0]]
CYC = [[Fr(int(i == (j + 1) % 4)) for j in range(4)] for i in range(4)]  # C e_j = e_{j+1}


def det(M):
    A = [row[:] for row in M]
    n, d = len(A), Fr(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]
            A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return d


def dyadic(q):
    q = abs(q)
    return q != 0 and q.numerator & (q.numerator - 1) == 0 and q.denominator & (q.denominator - 1) == 0


def matvec(M, v):
    return [sum(M[i][j] * v[j] for j in range(4)) for i in range(4)]


def cols(vs):
    return [[vs[j][i] for j in range(len(vs))] for i in range(4)]


def primitive(v):
    den = 1
    for x in v:
        den = den * Fr(x).denominator // math.gcd(den, Fr(x).denominator)
    ints = [int(Fr(x) * den) for x in v]
    g = 0
    for x in ints:
        g = math.gcd(g, x)
    return [Fr(x // g) for x in ints]


def small_combos(basis, k=2):
    """small integer combinations of the basis vectors (primitive), small entries first"""
    out = []
    for coefs in itertools.product(range(-k, k + 1), repeat=len(basis)):
        if any(coefs):
            v = primitive([sum(c * b[i] for c, b in zip(coefs, basis)) for i in range(4)])
            out.append(v)
    out.sort(key=lambda v: (sum(abs(x) for x in v), max(abs(x) for x in v)))
    seen, res = set(), []
    for v in out:
        key = tuple(v)
        neg = tuple(-x for x in v)
        if key not in seen and neg not in seen:
            seen.add(key)
            res.append(v)
    return res


def basis_X(X):
    """[b1, b2, w, Xw] with X b = b and X^2 w = -w, det dyadic, smallest entries first"""
    E1 = LT.nullspace([[X[i][j] - I4[i][j] for j in range(4)] for i in range(4)], 4)
    X2 = mm(X, X)
    E2 = LT.nullspace([[X2[i][j] + I4[i][j] for j in range(4)] for i in range(4)], 4)
    assert len(E1) == 2 and len(E2) == 2, (len(E1), len(E2))
    best = None
    c1, c2 = small_combos(E1), small_combos(E2)
    for b1, b2 in itertools.combinations(c1[:12], 2):
        for w in c2[:12]:
            B = cols([b1, b2, w, matvec(X, w)])
            d = det(B)
            if dyadic(d):
                cost = sum(abs(x) for row in B for x in row)
                if best is None or cost < best[0]:
                    best = (cost, B)
    return None if best is None else best[1]


def basis_cyc(Y):
    """[v, Yv, Y^2 v, Y^3 v] with det dyadic, smallest entries first"""
    best = None
    for coefs in itertools.product(range(-1, 2), repeat=4):
        if not any(coefs):
            continue
        v = [Fr(c) for c in coefs]
        vs = [v]
        for _ in range(3):
            vs.append(matvec(Y, vs[-1]))
        B = cols(vs)
        d = det(B)
        if dyadic(d):
            cost = sum(abs(x) for row in B for x in row)
            if best is None or cost < best[0]:
                best = (cost, B)
    return None if best is None else best[1]


def sandwich(T, X, Y, Z):
    g = (X, Y, Z, inv(X), inv(Y), inv(Z), [Fr(1)] * 48, [Fr(1)] * 48)
    return LT.apply(g, T, list(range(48)))


def lrp(T):
    return F.to_lrp(*T, True)


def side_floor(rows):
    keys, nonunit = set(), 0
    for row in rows:
        nz = [x for x in row if x != 0]
        if not nz:
            continue
        nonunit += sum(1 for x in nz if abs(x) != 1)
        if len(nz) == 1 and abs(nz[0]) == 1:
            continue
        s = 1 if nz[0] > 0 else -1
        keys.add(tuple(s * x for x in row))
    return len(keys), nonunit


def cost(T, lam):
    L, R, P = lrp(T)
    fl, nl = side_floor(L)
    fr, nr = side_floor(R)
    fp, np_ = side_floor([list(c) for c in zip(*P)])
    floor = fl + fr + fp + 32
    return floor + lam * (nl + nr + np_), floor, (fl, fr, fp), nl + nr + np_


def order4_elements(T):
    vc, pc = LT.colors(T)
    out = []
    for pi in LT.isomorphisms(vc, pc, vc, pc):
        g = LT.try_transport(T, T, pi)
        if g is None or S48.order_of(S48.cycle_type(pi)) != 4:
            continue
        Xn = []
        for M in g[:3]:
            s = next(x for r in M for x in r if x)
            Xn.append([[x / s for x in r] for r in M])
        out.append((Xn, pi))
    return out


def is_signed_perm_stab(T, Ms, pi):
    """does (S, C, C)-type element Ms map T onto itself with layer permutation pi?"""
    g = LT.try_transport(T, T, pi)
    if g is None:
        return False
    return all(S48.monomial(M) for M in g[:3])


def write_sms(prefix, T):
    L, R, P = lrp(T)
    for nm, M in (("L", L), ("R", R), ("P", P)):
        F.write_sms(f"{prefix}_{nm}.sms", M)


# ------------------------------------------------------------------ step 2: the symmetric family
def unit_zi_mats():
    """multiplication by the generators i and 1+i of Z[i][1/2]^* as 2x2 matrices (a I + b J)"""
    one, j = [[Fr(1), Fr(0)], [Fr(0), Fr(1)]], J2
    lin = lambda a, b: [[a * one[r][c] + b * j[r][c] for c in range(2)] for r in range(2)]
    return [lin(Fr(0), Fr(1)), lin(Fr(1), Fr(1)), lin(Fr(1, 2), Fr(-1, 2))]


def circulant(c):
    return [[Fr(c[(i - j) % 4]) for j in range(4)] for i in range(4)]


def circ_from_values(f1, fm1, fi):
    """the circulant with f(1) = f1, f(-1) = fm1, f(i) = fi (fi = (re, im)); coefficients dyadic"""
    re, im = fi
    # f(x) = c0 + c1 x + c2 x^2 + c3 x^3; inverse DFT over the 4th roots of unity
    vals = {1: (f1, 0), -1: (fm1, 0)}
    c = []
    for k in range(4):
        # c_k = (1/4) sum_w f(w) w^-k, w in {1, i, -1, -i}; f(-i) = conj f(i)
        s_re = Fr(f1) + Fr(fm1) * (-1) ** k
        # w = i: f(i) i^-k ; w = -i: conj(f(i)) (-i)^-k = conj(f(i) i^-k); sum = 2 Re(f(i) i^-k)
        ik = [(1, 0), (0, -1), (-1, 0), (0, 1)][k]  # i^-k
        s_re += 2 * (Fr(re) * ik[0] - Fr(im) * ik[1])
        c.append(s_re / 4)
    return circulant(c)


def circ_generators():
    gens = []
    for f1, fm1, fi in ((2, 1, (1, 0)), (-1, 1, (1, 0)), (1, 2, (1, 0)), (1, -1, (1, 0)),
                        (1, 1, (0, 1)), (1, 1, (1, 1))):
        M = circ_from_values(f1, fm1, fi)
        gens.append(M)
        gens.append(inv(M))
    return gens


def x_generators():
    gens = []
    blk = lambda A, Bm: [[A[r][c] if r < 2 and c < 2 else (Bm[r - 2][c - 2] if r >= 2 and c >= 2 else Fr(0))
                          for c in range(4)] for r in range(4)]
    one2 = [[Fr(1), Fr(0)], [Fr(0), Fr(1)]]
    for cf in (Fr(1), Fr(-1), Fr(2), Fr(-2), Fr(1, 2), Fr(-1, 2)):
        for (i, j) in ((0, 1), (1, 0)):
            E = [[Fr(int(r == c)) for c in range(2)] for r in range(2)]
            E[i][j] = cf
            gens.append(blk(E, one2))
    gens.append(blk([[Fr(0), Fr(1)], [Fr(1), Fr(0)]], one2))
    gens.append(blk([[Fr(2), Fr(0)], [Fr(0), Fr(1)]], one2))
    gens.append(blk([[Fr(1, 2), Fr(0)], [Fr(0), Fr(1)]], one2))
    for M in unit_zi_mats():
        gens.append(blk(one2, M))
    return gens


def anneal(T0, kinds, lam, steps, rng, t0=2.0, t1=0.2):
    gens = {"cyc": circ_generators(), "fix2swap": x_generators()}
    T = T0
    cur = cost(T, lam)
    best = (cur, T)
    for s in range(steps):
        temp = t0 * (t1 / t0) ** (s / max(1, steps - 1))
        slot = rng.randrange(3)
        M = rng.choice(gens[kinds[slot]])
        X, Y, Z = (M if slot == 0 else I4), (M if slot == 1 else I4), (M if slot == 2 else I4)
        T2 = sandwich(T, X, Y, Z)
        if max(abs(x) for D in T2 for Mk in D for row in Mk for x in row) > 8:
            continue
        c2 = cost(T2, lam)
        if c2[0] <= cur[0] or rng.random() < math.exp((cur[0] - c2[0]) / temp):
            T, cur = T2, c2
            if cur[0] < best[0][0]:
                best = (cur, T)
    return best


CP_CYC = (1, 0, 0, 0, -1)
CP_FIX = (1, -2, 2, -2, 1)
CP_FIXNEG = (1, 2, 2, 2, 1)


def charpoly(M):
    n = 4
    c = [Fr(1)]
    Mk = [[Fr(0)] * n for _ in range(n)]
    for k in range(1, n + 1):
        Mk = [[sum(M[i][t] * Mk[t][j] for t in range(n)) + (c[-1] if i == j else 0) for j in range(n)]
              for i in range(n)]
        MM = mm(M, Mk)
        c.append(-sum(MM[i][i] for i in range(n)) / k)
    return tuple(int(x) for x in c)


def adapted(M):
    """(kind, B, target) with B^-1 M B = target, det B dyadic; None if not found"""
    cp = charpoly(M)
    if cp == CP_FIXNEG:
        M = [[-x for x in row] for row in M]
        cp = CP_FIX
    if cp == CP_CYC:
        B = basis_cyc(M)
        return None if B is None else ("cyc", B, CYC, M)
    if cp == CP_FIX:
        B = basis_X(M)
        return None if B is None else ("fix2swap", B, S_X, M)
    return None


def orbits(pi):
    seen, out = set(), []
    for k in range(48):
        if k not in seen:
            cyc, j = [], k
            while j not in seen:
                seen.add(j)
                cyc.append(j)
                j = pi[j]
            out.append(cyc)
    return out


def cyc_basis_from(M, v):
    vs = [v]
    for _ in range(3):
        vs.append(matvec(M, vs[-1]))
    B = cols(vs)
    return B if dyadic(det(B)) else None


def rowvec(M):
    for row in M:
        if any(row):
            return list(row)
    raise ValueError("zero matrix")


def dual_cyc_basis_from(M, q):
    """B = D^-T for D = [q, M^-T q, M^-2T q, M^-3T q]: B^-1 M B is again the 4-cycle, and the
    row vectors carried along by M^-T become unit vectors"""
    MiT = LT.T(inv(M))
    vs = [q]
    for _ in range(3):
        vs.append(matvec(MiT, vs[-1]))
    D = cols(vs)
    if not dyadic(det(D)):
        return None
    return LT.T(inv(D))


def structured_candidates(T, Ms, pi):
    """per slot, the bases from the scheme's own rank-1 vectors, one per orbit of rank-1 layers:
    primal (factor columns carried by M: u of U for X, r of V for Y, p of W for Z) and dual
    (factor rows carried by M^-T: q of W for X, v of U for Y, s of V for Z)"""
    U, V, W = T
    reps = [o[0] for o in orbits(pi) if F.rank(U[o[0]]) == 1]
    prim = [U, V, W]
    dual = [W, U, V]
    out = []
    for slot in range(3):
        bs = []
        for k in reps:
            B = cyc_basis_from(Ms[slot], primitive(LT.colvec(prim[slot][k])))
            if B is not None:
                bs.append(B)
            B = dual_cyc_basis_from(Ms[slot], primitive(rowvec(dual[slot][k])))
            if B is not None:
                assert mm(mm(inv(B), Ms[slot]), B) == CYC
                bs.append(B)
        out.append(bs)
    return out


def score_combo(args):
    T, Bs, lam = args
    T1 = sandwich(T, *(inv(B) for B in Bs))
    return cost(T1, lam), Bs


def structured(T, Ms, pi, lam, keep=12, jobs=12):
    cands = structured_candidates(T, Ms, pi)
    combos = list(itertools.product(*cands))
    from concurrent.futures import ProcessPoolExecutor
    with ProcessPoolExecutor(jobs) as ex:
        scored = list(ex.map(score_combo, [(T, Bs, lam) for Bs in combos], chunksize=16))
    scored.sort(key=lambda t: t[0][0])
    top = [(c, sandwich(T, *(inv(B) for B in Bs))) for c, Bs in scored[:keep]]
    return top, len(combos), [len(c) for c in cands]


def run_restart(args):
    T0, kinds, lam, steps, seed, k = args
    bc, bT = anneal(T0, kinds, lam, steps, random.Random(seed))
    assert C.brent(*lrp(bT)) == 0
    return bc, bT, k, kinds


def main():
    prefix, outdir = sys.argv[1], sys.argv[2]
    opt = lambda k, d: type(d)(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else d
    steps, restarts, lam, seed = opt("--steps", 0), opt("--restarts", 1), opt("--lam", 0.1), opt("--seed", 1)
    os.makedirs(outdir, exist_ok=True)
    U, V, W = F.read_lrp(prefix)
    T = (U, V, [LT.T(M) for M in W])
    assert C.brent(*lrp(T)) == 0
    c0 = cost(T, lam)
    print(f"{os.path.basename(prefix)}: floor {c0[1]} = {'/'.join(map(str, c0[2]))} + 32, "
          f"{c0[3]} coefficients not in {{0, +-1}}")
    elems = order4_elements(T)
    print(f"{len(elems)} order-4 elements with trivial slot map")
    built = []
    for k, ((X, Y, Z), pi) in enumerate(elems):
        ad = [adapted(M) for M in (X, Y, Z)]
        if any(a is None for a in ad):
            print(f"  element {k}: no adapted basis with dyadic determinant among small vectors")
            continue
        for kind, B, tgt, M in ad:
            assert mm(mm(inv(B), M), B) == tgt
        P, Q, R = (inv(a[1]) for a in ad)
        kinds = tuple(a[0] for a in ad)
        T1 = sandwich(T, P, Q, R)
        assert C.brent(*lrp(T1)) == 0, "symmetric point fails Brent"
        assert is_signed_perm_stab(T1, None, pi), "the conjugated element is not a signed permutation"
        c1 = cost(T1, lam)
        built.append((c1, k, T1, kinds))
        print(f"  element {k} {'/'.join(kinds)}: symmetric point floor {c1[1]} = {'/'.join(map(str, c1[2]))} + 32, "
              f"{c1[3]} non-unit coefficients, max |entry| "
              f"{max(abs(x) for D in T1 for Mk in D for row in Mk for x in row)}")
    if not built:
        return
    if "--structured" in sys.argv:
        sbuilt = []
        for k, ((X, Y, Z), pi) in enumerate(elems):
            ad = [adapted(M) for M in (X, Y, Z)]
            if any(a is None for a in ad) or any(a[0] != "cyc" for a in ad):
                continue
            top, n, per = structured(T, [a[3] for a in ad], pi, lam)
            if not top:
                print(f"  element {k} cyc/cyc/cyc: no structured bases (candidates per slot {per})")
                continue
            for c1, T1 in top:
                assert C.brent(*lrp(T1)) == 0 and is_signed_perm_stab(T1, None, pi)
                sbuilt.append((c1, k, T1, ("cyc", "cyc", "cyc")))
            c1 = top[0][0]
            print(f"  element {k} cyc/cyc/cyc, {n} structured combinations (per slot {per}): best floor "
                  f"{c1[1]} = {'/'.join(map(str, c1[2]))} + 32, {c1[3]} non-units", flush=True)
        built = sorted(sbuilt, key=lambda t: t[0][0]) + built
    built.sort(key=lambda t: t[0][0])
    write_sms(f"{outdir}/sym_built", built[0][2])
    if steps:
        from concurrent.futures import ProcessPoolExecutor
        jobs = [(b[2], b[3], lam, steps, seed + r, b[1]) for r, b in
                ((r, built[r % len(built)]) for r in range(restarts))]
        results = []
        with ProcessPoolExecutor(opt("--jobs", 12)) as ex:
            for bc, bT, k, kinds in ex.map(run_restart, jobs):
                results.append((bc, bT, k))
                print(f"  restart from element {k} {'/'.join(kinds)}: best floor {bc[1]} = "
                      f"{'/'.join(map(str, bc[2]))} + 32, {bc[3]} non-units, objective {bc[0]:.1f}",
                      flush=True)
        results.sort(key=lambda t: t[0][0])
        for i, (bc, bT, k) in enumerate(results[:5]):
            write_sms(f"{outdir}/sym_best{i}", bT)
        print(f"best symmetric point: floor {results[0][0][1]}, {results[0][0][3]} non-units "
              f"(written to {outdir}/sym_best0_*.sms)")


if __name__ == "__main__":
    main()
