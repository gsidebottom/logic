# Check every claim of RFC 2610 that the published files can decide, with no answer from the author:
# the isotropies (1), (3), (4), rho, (9)-(11), g2, g13, g14 and the permutations pi, trying all six
# elements of S3 and the four forms M, M^-1, M^T, M^-T of each printed isotropy.
# A scheme is a list of triads (X, Y, Z) with T = sum e_ab o e_bc o e_ca, Z = P column reshaped, transposed.
import sys, itertools, warnings
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
import numpy as np
from fractions import Fraction as Fr
warnings.filterwarnings("ignore")
data, f203 = sys.argv[1], sys.argv[2]
def read_sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = np.zeros((r, c))
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1, int(t[1]) - 1] = float(Fr(t[2]))
    return M
def scheme(prefix):
    L, R, P = (read_sms(f"{prefix}_{m}.sms") for m in "LRP")
    return [(L[i].reshape(4, 4), R[i].reshape(4, 4), P[:, i].reshape(4, 4).T) for i in range(48)]
def iso(S, U, V, W):
    Ui, Vi, Wi = np.linalg.inv(U).T, np.linalg.inv(V).T, np.linalg.inv(W).T
    return [(Ui @ X @ V.T, Vi @ Y @ W.T, Wi @ Z @ U.T) for X, Y, Z in S]
def cyc(S): return [(Y, Z, X) for X, Y, Z in S]
def tau(S): return [(Y.T, X.T, Z.T) for X, Y, Z in S]
S3 = {"id": lambda S: S, "c": cyc, "c2": lambda S: cyc(cyc(S)), "t": tau, "tc": lambda S: tau(cyc(S)), "tc2": lambda S: tau(cyc(cyc(S)))}
TARGET = np.zeros((4,) * 6)
for a, b, c in itertools.product(range(4), repeat=3): TARGET[a, b, b, c, c, a] = 1
def tensor_ok(S):
    return np.abs(sum(np.einsum('ab,cd,ef->abcdef', X, Y, Z) for X, Y, Z in S) - TARGET).max() < 1e-7
def nrm(M):
    nz = M.ravel()[np.abs(M.ravel()) > 1e-9]; return tuple((np.round(M / nz[0], 6) + 0.0).ravel().tolist()), nz[0]
def keys(S):
    out = {}
    for i, (X, Y, Z) in enumerate(S):
        a, s1 = nrm(X); b, s2 = nrm(Y); c, s3 = nrm(Z)
        out[(a, b, c, round(s1 * s2 * s3, 6) + 0.0)] = i
    return out
A = lambda m: np.array(m, float)
I = np.eye(4)
G = {"(1)": (A([[1,1,-1,1],[1,-1,-1,1],[1,-1,-1,-1],[1,-1,1,-1]]), A([[0,0,1,1],[1,-1,0,0],[1,0,1,0],[1,0,-1,0]]), A([[1,-1,0,1],[1,0,0,1],[0,1,-1,0],[1,-1,1,0]])),
     "(3)": (I, A([[1,0,0,0],[0,1,-1,0],[0,0,1,0],[0,0,0,1]]), I),
     "(4)": (A([[0,1,0,0],[0,0,1,0],[0,0,0,1],[1,0,0,0]]), A([[0,0,1,0],[0,-1,0,0],[1,0,0,0],[0,0,0,1]]), A([[0,-1,0,0],[0,0,1,0],[0,0,0,-1],[1,0,0,0]])),
     "rho": (A([[0,1,0,0],[0,0,1,0],[0,0,0,1],[1,0,0,0]]), A([[0,0,1,0],[-1,-1,0,0],[1,0,0,0],[0,0,0,1]]), A([[0,-1,0,0],[0,0,1,0],[0,0,0,-1],[1,0,0,0]])),
     "id": (I, I, I)}
ST = {"(9)": (A([[0,1,0,0],[0,0,-1,0],[1,0,0,0],[0,0,0,1]]), A([[0,0,1,0],[1,0,0,0],[0,-1,0,0],[0,0,0,1]]), A([[1,0,0,0],[0,-1,0,0],[0,0,1,0],[0,0,0,-1]])),
      "(10)": (A([[0,0,1,0],[1,0,0,0],[0,-1,0,0],[0,0,0,1]]), A([[1,0,0,0],[0,-1,0,0],[0,0,1,0],[0,0,0,-1]]), A([[0,1,0,0],[0,0,-1,0],[1,0,0,0],[0,0,0,1]])),
      "(11)": (A([[0,0,0,1],[1,0,0,0],[0,0,-1,0],[0,1,0,0]]), A([[1,1,0,0],[1,0,0,0],[0,0,1,0],[0,0,0,-1]]), A([[0,1,0,0],[0,0,0,1],[0,0,-1,0],[1,0,0,0]])),
      "g2": (A([[0,0,0,1],[1,-1,0,1],[-1,0,1,1],[1,0,0,0]]), A([[-1,1,1,-1],[0,1,0,0],[0,0,1,0],[0,0,0,1]]), A([[0,0,1,0],[0,0,0,-1],[-1,0,0,0],[0,1,0,0]])),
      "g13": (A([[0,1,0,0],[1,0,0,0],[-1,1,1,0],[1,-1,0,1]]), A([[-1,1,1,-1],[0,0,1,-1],[0,1,0,1],[0,0,0,1]]), A([[0,0,0,1],[0,0,-1,0],[0,-1,0,0],[1,0,0,0]])),
      "g14": (A([[-1,1,0,-1],[0,0,0,-1],[0,1,-1,-1],[0,-1,0,0]]), A([[1,0,0,0],[0,0,1,-1],[0,1,0,1],[0,0,0,1]]), A([[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]))}
FORMS = {"M": lambda M: M, "M^-1": np.linalg.inv, "M^T": lambda M: M.T, "M^-T": lambda M: np.linalg.inv(M).T}
pts = {n: scheme(f"{data}/4x4x4_48_{n}") for n in ("rational", "204", "202", "201")}
pts["203"] = scheme(f"{f203}/4x4x4_48_203")
print("== gate: every point and action fixes the matrix multiplication tensor ==")
gate = [tensor_ok(S) for S in pts.values()] + [tensor_ok(f(pts["201"])) for f in S3.values()] + [tensor_ok(iso(pts["201"], *G["rho"])), tensor_ok(iso(pts["201"], *ST["g2"]))]
print(f"   {sum(gate)} of {len(gate)} checks pass")
print("== where the printed isotropies lead (best match per isotropy and source; 48 = identical scheme) ==")
tk = {(n, s): keys(f(S)) for n, S in pts.items() for s, f in S3.items()}
rows = {}
for src, S in pts.items():
    for s1, f in S3.items():
        Sf = f(S)
        for g, gm in G.items():
            for fn, form in FORMS.items():
                im = keys(iso(Sf, *map(form, gm)))
                for (t, s2), kt in tk.items():
                    if t == src and g == "id": continue
                    m = len(im.keys() & kt.keys())
                    k = (g, src, t)
                    if m > rows.get(k, (-1,))[0]: rows[k] = (m, s1, fn, s2)
for (g, src, t), (m, s1, fn, s2) in sorted(rows.items(), key=lambda kv: (kv[0][0], -kv[1][0])):
    if m >= 13: print(f"   {g:4s} {src:9s}-> {t:9s}: {m:2d}/48  (S3 {s1} on source, form {fn}, S3 {s2} on target)")
print("== canonical rows after (1) on the rational point (L, R, P columns) ==")
for fn, form in FORMS.items():
    im = iso(pts["rational"], *map(form, G["(1)"]))
    canon = [sum(1 for t in im if (np.abs(t[j]) > 1e-9).sum() == 1) for j in range(3)]
    print(f"   form {fn}: {canon}")
print("== stabilizers: printed element fixes a point (all forms and S3 tried) ==")
pi = {"pi2": [(1,29),(2,42),(3,39),(4,17),(5,46),(6,16),(7,43),(8,11),(9,28),(10,23),(12,19),(13,37),(14,27),(15,48),(18,41),(20,36),(21,31),(22,32),(24,26),(25,35),(30,47),(33,45),(34,40),(38,44)],
      "pi3": [(1,11),(2,43),(3,31),(4,38),(5,41),(6,45),(7,42),(8,29),(9,22),(10,47),(12,25),(13,27),(14,37),(15,40),(16,33),(17,44),(18,46),(19,35),(20,26),(21,39),(23,30),(24,36),(28,32),(34,48)],
      "pi4": [(1,8),(2,7),(3,21),(4,44),(5,18),(6,33),(9,32),(10,30),(11,29),(12,35),(13,14),(15,34),(16,45),(17,38),(19,25),(20,24),(22,28),(23,47),(26,36),(27,37),(31,39),(40,48),(41,46),(42,43)]}
perm = {n: {x: y for a, b in p for x, y in ((a, b), (b, a))} for n, p in pi.items()}
print("   pi are fixed-point-free involutions:", all(len(p) == 48 and all(p[p[i]] == i for i in p) for p in perm.values()))
print("   pi2 pi3 == pi4:", all(perm["pi3"][perm["pi2"][i]] == perm["pi4"][i] for i in perm["pi2"]), "| pi3(8) =", perm["pi3"][8], "| pi4(8) =", perm["pi4"][8])
for g, gm in ST.items():
    best = (0,)
    for p, S in pts.items():
        k0 = keys(S)
        for s, f in S3.items():
            for fn, form in FORMS.items():
                im = keys(iso(f(S), *map(form, gm)))
                m = len(im.keys() & k0.keys())
                if m > best[0]:
                    best = (m, p, s, fn, {im[k] + 1: k0[k] + 1 for k in im.keys() & k0.keys()})
    line = f"   {g:5s} best {best[0]:2d}/48 on {best[1]} (S3 {best[2]}, form {best[3]})" if best[0] else f"   {g:5s} best 0/48"
    if best[0] == 48:
        same = [n for n, p in perm.items() if all(p[i] == best[4][i] for i in p)]
        line += f"; permutation equals {same or 'none of the printed'}"
    print(line)
