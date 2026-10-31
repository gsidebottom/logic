# RFC 2610: the suffixes o k restated on the note's own [L; R; P], with no X, Y, Z.  Sedoglavic replied
# that he does not know what X, Y, Z are, and his note has none: they were 4 x 4 matrices per product,
# row k of L, row k of R and column k of P reshaped, the last transposed.  K is the 16 x 16 commutation
# matrix, K vec(M) = vec(M^T).  Each map is checked by itself: on every point it must multiply matrices
# (read directly as vec(AB) = P (L vec A * R vec B), 16^3 equations, nothing about traces), it must equal
# the triad form in verify_note.py, and exactly one of the six may reproduce each printed o k.
import sys
src = open(sys.argv[3]).read(); exec(src[:src.index('print("== gate')])
lam = scheme(sys.argv[4])
inv = np.linalg.inv
def lrp(S): return np.array([t[0].ravel() for t in S]), np.array([t[1].ravel() for t in S]), np.array([t[2].T.ravel() for t in S]).T
def tri(L, R, P): return [(L[i].reshape(4, 4), R[i].reshape(4, 4), P[:, i].reshape(4, 4).T) for i in range(48)]
K = np.zeros((16, 16))
for a, b in itertools.product(range(4), repeat=2): K[b * 4 + a, a * 4 + b] = 1
M0 = np.arange(16.).reshape(4, 4); assert np.array_equal(K @ M0.ravel(), M0.T.ravel())
E = np.zeros((16, 16, 16))
for a, b, c in itertools.product(range(4), repeat=3): E[a * 4 + b, b * 4 + c, a * 4 + c] = 1
def computes(L, R, P): return np.abs(np.einsum('ki,kj,lk->ijl', L, R, P) - E).max() == 0
def lemma21(L, R, P, U, V, W): return L @ np.kron(inv(U), V.T), R @ np.kron(inv(V), W.T), np.kron(U, inv(W).T) @ P
ACT = {"[L; R; P]":          (lambda L, R, P: (L, R, P),                "id"),
       "[R K; L K; K P]":    (lambda L, R, P: (R @ K, L @ K, K @ P),    "t"),
       "[R; P^T K; K L^T]":  (lambda L, R, P: (R, P.T @ K, K @ L.T),    "c"),
       "[L K; P^T; R^T]":    (lambda L, R, P: (L @ K, P.T, R.T),        "tc2"),
       "[P^T K; L; K R^T]":  (lambda L, R, P: (P.T @ K, L, K @ R.T),    "c2"),
       "[P^T; R K; L^T]":    (lambda L, R, P: (P.T, R @ K, L.T),        "tc")}
rat1 = iso(pts["rational"], *G["(1)"])
P_ = {"rational": pts["rational"], "(1)": rat1, "204": pts["204"], "203": pts["203"], "202": pts["202"], "201": pts["201"], "lam01c0": lam}
print("== gates ==")
print("   every point multiplies matrices, read directly:", all(computes(*lrp(S)) for S in P_.values()), f"({len(P_)} points)")
print("   each of the six maps, on every point, still multiplies matrices:", all(computes(*f(*lrp(S))) for f, _ in ACT.values() for S in P_.values()))
print("   each map equals its triad form exactly:", all(all(np.array_equal(a, b) for a, b in zip(f(*lrp(S)), lrp(S3[s](S)))) for f, s in ACT.values() for S in P_.values()))
print("   Lemma 2.1 on [L; R; P] equals the triad action:", all(np.allclose(a, b) for g in list(G.values()) + list(ST.values()) for a, b in zip(lemma21(*lrp(lam), *g), lrp(iso(lam, *g)))))
exact = lambda A, B: len(keys(A).keys() & keys(B).keys())
print("== which of the six maps reproduces each printed o k (48 = same scheme); isotropy after the map ==")
print(f"   {'':34s}" + "".join(f"{n:>19s}" for n in ACT))
def row(name, target, src, g):
    print(f"   {name:34s}" + "".join(f"{exact(tri(*lemma21(*f(*lrp(src)), *g)), target):19d}" for f, _ in ACT.values()))
I3 = (I, I, I)
row("(2)  (1) point -> 204", pts["204"], rat1, I3)
row("(2)  (1) point -> 203 files", pts["203"], rat1, I3)
row("(9)  fixes the (1) point", rat1, rat1, ST["(9)"])
row("(10) fixes 204", pts["204"], pts["204"], ST["(10)"])
row("(10) fixes 203 files", pts["203"], pts["203"], ST["(10)"])
row("(11) fixes lam01c0_201", lam, lam, ST["(11)"])
print("== the other order: isotropy first, then the map ==")
print(f"   {'':34s}" + "".join(f"{n:>19s}" for n in ACT))
def row2(name, target, src, g):
    print(f"   {name:34s}" + "".join(f"{exact(tri(*f(*lemma21(*lrp(src), *g))), target):19d}" for f, _ in ACT.values()))
row2("(9)  fixes the (1) point", rat1, rat1, ST["(9)"])
row2("(10) fixes 204", pts["204"], pts["204"], ST["(10)"])
row2("(11) fixes lam01c0_201", lam, lam, ST["(11)"])
print("== (10) is (9) conjugated by the rotation ==")
print("   (U, V, W) of (10) = (V, W, U) of (9):", all(np.array_equal(a, b) for a, b in zip(ST["(10)"], (ST["(9)"][1], ST["(9)"][2], ST["(9)"][0]))))
