#!/usr/bin/env python3
"""Gauge/orbit search over VERIFIED 4x4 schemes.

For invertible P, Q, R the substitution A -> P A Q^-1, B -> Q B R^-1
sends C -> P C R^-1, so a scheme (alpha, beta, gamma) maps to

    alpha -> P^-T alpha Q^T,  beta -> Q^-T beta R^T,  gamma -> P gamma R^-1

which is again an exact scheme.  Every image is therefore valid by
construction (and re-verified here by exact evaluation).  Unimodular
P,Q,R keep everything integral; the images have DIFFERENT linear maps,
so different online add counts -- the search space this explores.

Online floor = #distinct multi-term rows on the two live sides
+ (nonzero products - 16) + #non-unit coefficients on those sides.
"""
import itertools, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mk49 import strassen2, kron, gate, write_sms

N = 4

def mat_mul(A, B):
    return [[sum(A[i][k]*B[k][j] for k in range(N)) for j in range(N)]
            for i in range(N)]

def mat_T(A):
    return [[A[j][i] for j in range(N)] for i in range(N)]

def mat_inv_unimodular(A):
    """exact inverse of an integer matrix with det = +-1 (adjugate/det)."""
    from fractions import Fraction
    n = N
    M = [[Fraction(A[i][j]) for j in range(n)] + [Fraction(int(i == j)) for j in range(n)]
         for i in range(n)]
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, n) if M[i][c] != 0), None)
        if piv is None: return None
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(n):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f*y for x, y in zip(M[i], M[r])]
        r += 1
    inv = [[M[i][n+j] for j in range(n)] for i in range(n)]
    if any(x.denominator != 1 for row in inv for x in row): return None
    return [[int(x) for x in row] for row in inv]

def rand_unimodular(rng, nops=2):
    """product of a few elementary row ops -> unimodular, small entries."""
    M = [[int(i == j) for j in range(N)] for i in range(N)]
    for _ in range(nops):
        i, j = rng.sample(range(N), 2)
        s = rng.choice((1, -1))
        for c in range(N):
            M[i][c] += s * M[j][c]
    return M

def dict_to_mat(d):
    M = [[0]*N for _ in range(N)]
    for (i, j), v in d.items(): M[i][j] = v
    return M

def mat_to_dict(M):
    return {(i, j): M[i][j] for i in range(N) for j in range(N) if M[i][j]}

def act(al, be, ga, P, Q, R):
    Pi, Qi, Ri = (mat_inv_unimodular(X) for X in (P, Q, R))
    if Pi is None or Qi is None or Ri is None: return None
    PiT, QiT = mat_T(Pi), mat_T(Qi)
    QT, RT = mat_T(Q), mat_T(R)
    A2 = [mat_to_dict(mat_mul(mat_mul(PiT, dict_to_mat(a)), QT)) for a in al]
    B2 = [mat_to_dict(mat_mul(mat_mul(QiT, dict_to_mat(b)), RT)) for b in be]
    G2 = [mat_to_dict(mat_mul(mat_mul(P, dict_to_mat(g)), Ri)) for g in ga]
    return A2, B2, G2

def online_floor(al, be, ga):
    """min over 6 orientations of (live-side adds floor + scalar mults)."""
    T = lambda d: {(j, i): v for (i, j), v in d.items()}
    tri = [(al[m], be[m], T(ga[m])) for m in range(len(al))]
    cyc = lambda t: [(b, c, a) for (a, b, c) in t]
    swp = [(T(b), T(a), T(c)) for (a, b, c) in tri]
    best = None
    for var in (tri, cyc(tri), cyc(cyc(tri)), swp, cyc(swp), cyc(cyc(swp))):
        bs = [x[1] for x in var]
        gs = [T(x[2]) for x in var]
        key = lambda d: tuple(sorted(d.items()))
        nt_b = len({key(d) for d in bs if len(d) >= 2})
        nt_c = len({key(d) for d in gs if len(d) >= 2})
        nzp = sum(1 for g in gs if g)
        mults = sum(1 for d in bs + gs for v in d.values() if abs(v) != 1)
        fl = nt_b + nt_c + (nzp - N*N) + mults
        best = fl if best is None else min(best, fl)
    return best

if __name__ == "__main__":
    seed_al, seed_be, seed_ga = kron(*strassen2())
    assert gate(seed_al, seed_be, seed_ga, n=4)
    base = online_floor(seed_al, seed_be, seed_ga)
    print(f"Strassen^2-49 seed: online floor {base} (PLinOpt achieved 145)")
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    best, bestimg, hits = base, None, 0
    for t in range(trials):
        nops = rng.choice((1, 1, 2, 2, 3))
        P, Q, R = (rand_unimodular(rng, nops) for _ in range(3))
        img = act(seed_al, seed_be, seed_ga, P, Q, R)
        if img is None: continue
        hits += 1
        fl = online_floor(*img)
        if fl < best:
            assert gate(*img, n=4), "gauge image must still compute matmul"
            best, bestimg = fl, (img, P, Q, R)
            print(f"  trial {t}: NEW BEST online floor {fl} (was {base})")
    print(f"{hits} valid images; best online floor {best} (seed {base})")
    if bestimg:
        import json
        img, P, Q, R = bestimg
        json.dump({"P": P, "Q": Q, "R": R}, open("matmul/asym4/gauge_best.json", "w"))
        print("saved gauge_best.json")
