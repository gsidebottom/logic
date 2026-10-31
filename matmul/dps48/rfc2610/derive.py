# Derive the isotropy between the 203 point and our 201 point from the data, without using rho.
import sys, itertools, warnings
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
import numpy as np
from collections import Counter
from fractions import Fraction as Fr
warnings.filterwarnings("ignore")
sys.setrecursionlimit(10000)
def read_sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = np.zeros((r, c))
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1, int(t[1]) - 1] = float(Fr(t[2]))
    return M
def nkey(v):
    nz = v[np.abs(v) > 1e-9]; return tuple(np.round(v / nz[0], 6) + 0.0)
d3, d1 = sys.argv[1], sys.argv[2]
L3, R3, P3 = (read_sms(f"{d3}/4x4x4_48_203_{m}.sms") for m in "LRP")
L1, R1, P1 = (read_sms(f"{d1}/4x4x4_48_201_{m}.sms") for m in "LRP")
S3, S1 = P3 != 0, P1 != 0
print("P nonzeros per row, sorted: 203", sorted(S3.sum(1).tolist()), "\n                            201", sorted(S1.sum(1).tolist()))
isos = []
def extend(m):
    t = len(m)
    if len(isos) >= 20000: return
    if t == 16: isos.append(list(m)); return
    for r in range(16):
        if r in m or S3[t].sum() != S1[r].sum(): continue
        m2 = m + [r]
        if Counter(map(tuple, S3[:t+1, :].T.tolist())) == Counter(map(tuple, S1[m2, :].T.tolist())): extend(m2)
extend([])
print("support isomorphisms of P (rows of 203 -> rows of 201):", len(isos))
kron_ok = []
for m in isos:
    f, g = {}, {}; ok = True
    for r in range(16):
        a, c = r // 4, r % 4; a2, c2 = m[r] // 4, m[r] % 4
        if f.setdefault(a, a2) != a2 or g.setdefault(c, c2) != c2: ok = False; break
    if ok: kron_ok.append((f, g))
print("of these, of Kronecker form U x W^-T:", len(kron_ok))
col1 = {}
for j in range(48): col1[nkey(P1[:, j])] = j
found = []
for f, g in kron_ok:
    for su in itertools.product((1, -1), repeat=4):
        for st in itertools.product((1, -1), repeat=4):
            U = np.zeros((4, 4)); T = np.zeros((4, 4))
            for a in range(4): U[f[a], a] = su[a]
            for c in range(4): T[g[c], c] = st[c]
            PP = np.kron(U, T) @ P3
            pi = [col1.get(nkey(PP[:, i]), -1) for i in range(48)]
            if -1 not in pi and len(set(pi)) == 48: found.append((U, T, pi, PP))
print("signed Kronecker maps taking 203's P columns onto 201's:", len(found))
solved = 0
for U, T, pi, PP in found:
    Ui = np.linalg.inv(U); Wt = np.linalg.inv(T)
    A = np.zeros((48 * 16, 16 + 48))
    for i in range(48):
        X = Ui.T @ L3[i].reshape(4, 4); Xo = L1[pi[i]].reshape(4, 4)
        for p in range(4):
            for q in range(4):
                row = i * 16 + p * 4 + q
                for r in range(4): A[row, r * 4 + q] = X[p, r]
                A[row, 16 + i] = -Xo[p, q]
    s = np.linalg.svd(A, compute_uv=True)
    sv, Vh = s[1], s[2]
    if sv[-1] > 1e-9: continue
    x = Vh[-1]; G = x[:16].reshape(4, 4); tau = x[16:]
    if abs(np.linalg.det(G)) < 1e-9 or np.min(np.abs(tau)) < 1e-9: continue
    G = G / np.max(np.abs(G)); Gi = np.linalg.inv(G)
    a = []; b = []; c = []
    for i in range(48):
        X = Ui.T @ L3[i].reshape(4, 4) @ G; Xo = L1[pi[i]].reshape(4, 4); a.append(np.sum(X * Xo) / np.sum(Xo * Xo))
        Y = Gi @ R3[i].reshape(4, 4) @ Wt; Yo = R1[pi[i]].reshape(4, 4); b.append(np.sum(Y * Yo) / np.sum(Yo * Yo))
        C = PP[:, i]; Co = P1[:, pi[i]]; c.append(np.sum(C * Co) / np.sum(Co * Co))
        if np.abs(X - a[-1] * Xo).max() > 1e-8 or np.abs(Y - b[-1] * Yo).max() > 1e-8: break
    else:
        solved += 1
        a, b, c = map(np.array, (a, b, c)); k = 1 / Counter(np.round(np.abs(a), 6)).most_common(1)[0][0]
        print("dimension of the solution space:", int((sv < 1e-9).sum()))
        print("U =", U.astype(int).tolist()); print("W =", np.linalg.inv(T).T.astype(int).tolist()); print("V (scaled to max 1) =", np.round(G.T, 4).tolist())
        rows = Counter((round(float(abs(k * x)), 4), round(float(abs(y / k)), 4), round(float(abs(z)), 4)) for x, y, z in zip(a, b, c))
        print("per-product scalars of the image over our 201, (|L|, |R|, |P|), with count:")
        for t, n in rows.most_common(): print("   ", t, n)
        sign = Counter((int(np.sign(x)), int(np.sign(y)), int(np.sign(z))) for x, y, z in zip(a, b, c))
        print("sign patterns:", dict(sign))
        break
print("maps with a consistent V and all 48 L and R rows matched:", solved)
