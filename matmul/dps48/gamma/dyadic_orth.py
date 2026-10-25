"""The whole dyadic orthogonal sub-orbit of a scheme, exhaustively: U, V, W in the group G of
4x4 orthogonal matrices with entries in Z[1/2] or Z[1/2]/sqrt2 (W(F4): signed permutations and
+-1/2 matrices, and the 1152 with entries 0, +-1/sqrt2; |G| = 2304).  Every (U, V, W) in G^3
gives a dyadic scheme after per-term rescaling (the sqrt2 factors pair up in each term), and
gamma_{inf,2}, gamma_{inf,inf} and the nonzero counts do not change when any factor is
multiplied on the left by a signed permutation: G has 6 classes, so 216 points per role."""
import itertools, sys
import numpy as np
np.seterr(all="ignore")
import orbit
from exact import q45_all, signed_perms, nnz

def hadamard_halves():
    """the 768 orthogonal matrices with entries +-1/2 (times 2: entries +-1, Q Q^T = 4 I)"""
    out = []
    rows = [np.array(v, dtype=float) for v in itertools.product([-1, 1], repeat=4)]
    def rec(acc):
        if len(acc) == 4:
            out.append(np.array(acc))
            return
        for v in rows:
            if all(np.dot(v, a) == 0 for a in acc):
                rec(acc + [v])
    rec([])
    return out

def group():
    """(Q, c2): the matrix is Q / sqrt(c2)"""
    return [(Q, 1) for Q in signed_perms()] + [(Q, 4) for Q in hadamard_halves()] + [(Q, 2) for Q in q45_all()]

def key(Q):
    """invariant of left multiplication by signed permutations: the set of rows up to sign"""
    rows = []
    for r in Q:
        nz = r[np.nonzero(r)[0][0]]
        rows.append(tuple((r * np.sign(nz)).astype(int)))
    return frozenset(rows)

def classes():
    seen = {}
    for Q, c2 in group():
        seen.setdefault(key(Q), (Q, c2))
    return list(seen.values())

def transformed(L, R, P, U, V, W):
    """exact dyadic scheme for U = QU/sqrt(cU2) etc. (orthogonal): L (U^T x V^T), R (V^T x W^T),
    (U x W) P, each term rescaled by the sqrt2 powers so all entries are dyadic"""
    (QU, cU), (QV, cV), (QW, cW) = U, V, W
    L2 = L @ np.kron(QU.T, QV.T)                  # times 1/sqrt(cU cV)
    R2 = R @ np.kron(QV.T, QW.T)                  # times 1/sqrt(cV cW)
    P2 = np.kron(QU, QW) @ P / (cU * cV * cW)     # carries all the constants: 1/sqrt(cU cW) * 1/sqrt(cU cV cV cW)
    return L2, R2, P2

if __name__ == "__main__":
    name = sys.argv[1] if len(sys.argv) > 1 else "table1"
    cl = classes()
    print(f"# |G| = {len(group())}, classes under signed permutations: {len(cl)}")
    base = orbit.load(orbit.SCHEMES[name])
    rows = []
    for role, (L, R, P) in enumerate(orbit.roles(*base)):
        for iu, iv, iw in itertools.product(range(len(cl)), repeat=3):
            L2, R2, P2 = transformed(L, R, P, cl[iu], cl[iv], cl[iw])
            assert orbit.brent_error(L2, R2, P2) < 1e-12
            rows.append((orbit.g_inf2(L2, R2, P2), orbit.g_inf_inf(L2, R2, P2), role, iu, iv, iw, nnz(L2), nnz(R2), nnz(P2)))
    rows.sort()
    print(f"# {name}: {len(rows)} points; distinct (g(inf,2), g(inf,inf)) pairs:")
    seen = set()
    for g2, gi, role, iu, iv, iw, a, b, c in rows:
        k = (round(g2, 4), round(gi, 2))
        if k in seen:
            continue
        seen.add(k)
        print(f"  g(inf,2) {g2:9.4f}  g(inf,inf) {gi:7.2f}   role {role} classes U{iu} V{iv} W{iw}  nnz {a}+{b}+{c} = {a + b + c}")
    # the Pareto front in (g(inf,2), g(inf,inf))
    front, best_gi = [], float("inf")
    for g2, gi, *rest in rows:
        if gi < best_gi - 1e-9:
            front.append((g2, gi, *rest))
            best_gi = gi
    print("# Pareto front (g(inf,2), g(inf,inf)):", "  ".join(f"({g2:.3f}, {gi:.1f}) r{r} U{u}V{v}W{w}" for g2, gi, r, u, v, w, *_ in front))
