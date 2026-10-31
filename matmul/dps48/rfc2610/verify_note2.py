# Follow-up to verify_note.py: every isotropy between the published points whose P parts differ by a
# signed Kronecker map, and the note's stabilizer elements on the points (1) and (4) actually produce.
import sys
src = open(sys.argv[3]).read(); exec(src[:src.index('print("== gate')])
from collections import Counter
def arrays(S): return np.array([t[0].ravel() for t in S]), np.array([t[1].ravel() for t in S]), np.array([t[2].T.ravel() for t in S]).T
def nkey(v):
    nz = v[np.abs(v) > 1e-9]; return tuple((np.round(v / nz[0], 6) + 0.0).tolist())
def maps(Sa, Sb):
    La, Ra, Pa = arrays(Sa); Lb, Rb, Pb = arrays(Sb)
    A, B = Pa != 0, Pb != 0; found = []; isos = []
    def ext(m):
        t = len(m)
        if t == 16: isos.append(list(m)); return
        for r in range(16):
            if r in m or A[t].sum() != B[r].sum(): continue
            m2 = m + [r]
            if Counter(map(tuple, A[:t+1].T.tolist())) == Counter(map(tuple, B[m2].T.tolist())): ext(m2)
    ext([])
    col = {nkey(Pb[:, j]): j for j in range(48)}
    for m in isos:
        f, g = {}, {}
        if any(f.setdefault(r // 4, m[r] // 4) != m[r] // 4 or g.setdefault(r % 4, m[r] % 4) != m[r] % 4 for r in range(16)): continue
        for su in itertools.product((1, -1), repeat=4):
            for st in itertools.product((1, -1), repeat=4):
                U, T = np.zeros((4, 4)), np.zeros((4, 4))
                for a in range(4): U[f[a], a] = su[a]; T[g[a], a] = st[a]
                PP = np.kron(U, T) @ Pa; pi = [col.get(nkey(PP[:, i]), -1) for i in range(48)]
                if -1 in pi or len(set(pi)) != 48: continue
                Ui = np.linalg.inv(U); M = np.zeros((768, 64))
                for i in range(48):
                    X = Ui.T @ La[i].reshape(4, 4); Xo = Lb[pi[i]].reshape(4, 4)
                    for p in range(4):
                        for q in range(4):
                            row = i * 16 + p * 4 + q
                            for r in range(4): M[row, r * 4 + q] = X[p, r]
                            M[row, 16 + i] = -Xo[p, q]
                _, sv, Vh = np.linalg.svd(M)
                if sv[-1] > 1e-9: continue
                Vt = Vh[-1][:16].reshape(4, 4)
                if abs(np.linalg.det(Vt)) < 1e-9: continue
                Vt = Vt / np.max(np.abs(Vt)); V = Vt.T; W = np.linalg.inv(T).T
                im = iso(Sa, U, V, W)
                pr = len({(nrm(t[0])[0], nrm(t[1])[0], nrm(t[2])[0]) for t in im} & {(nrm(t[0])[0], nrm(t[1])[0], nrm(t[2])[0]) for t in Sb})
                if pr == 48: found.append((U, V, W))
    return found
def signed_perm(M):
    M = M / np.max(np.abs(M)); return bool(((np.abs(M) > 1e-9).sum(0) == 1).all() and ((np.abs(M) > 1e-9).sum(1) == 1).all())
P0 = iso(pts["rational"], *G["(1)"])
pts.update({"(1)rat": P0, "(4)202": iso(pts["202"], *G["(4)"]), "(4)204": iso(pts["204"], *G["(4)"]), "rho204": iso(pts["204"], *G["rho"]), "(3)(4)204": iso(iso(pts["204"], *G["(4)"]), *G["(3)"])})
for a, b in (("202", "201"), ("203", "201"), ("(4)202", "201"), ("rho204", "201")):
    ms = maps(pts[a], pts[b])
    sp = [m for m in ms if signed_perm(m[1])]
    print(f"{a} -> {b}: {len(ms)} maps with a signed-permutation P part, {len(sp)} with V a signed permutation too")
    for U, V, W in (sp or ms)[:2]:
        print("   U", U.astype(int).tolist(), "\n   V", np.round(V / np.max(np.abs(V)), 3).tolist(), "\n   W", np.round(W, 3).astype(int).tolist())
print("(4) as printed: U", G["(4)"][0].astype(int).tolist(), "\n                V", G["(4)"][1].astype(int).tolist(), "\n                W", G["(4)"][2].astype(int).tolist())
print("== stabilizer elements on every point, form M, all S3; 48 = fixes the point ==")
for g, gm in ST.items():
    res = []
    for p, S in pts.items():
        k0 = keys(S)
        for s, f in S3.items():
            im = keys(iso(f(S), *gm)); m = len(im.keys() & k0.keys())
            if m: res.append((m, p, s, {im[k] + 1: k0[k] + 1 for k in im.keys() & k0.keys()}))
    res.sort(key=lambda r: -r[0])
    if not res: print(f"   {g:5s} matches nothing"); continue
    m, p, s, q = res[0]
    extra = ""
    if m == 48:
        order = 1; c = dict(q)
        while any(c[i] != i for i in c): c = {i: q[c[i]] for i in c}; order += 1
        extra = f", order of the permutation {order}, printed pi: {[n for n, pp in perm.items() if all(pp[i] == q[i] for i in pp)] if 'perm' in globals() else '-'}"
    print(f"   {g:5s} best {m}/48 on {p} (S3 {s}){extra}; also {[(r[0], r[1], r[2]) for r in res[1:4]]}")
