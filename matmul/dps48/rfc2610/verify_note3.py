# Third pass: rho's factor order, the 56 + 56 + 89 circuit at Ruchit's point, the pi numbering.
import sys, re
src2 = open(sys.argv[4]).read(); exec(src2[:src2.index('P0 = iso(')])
srcn = open(sys.argv[3]).read(); exec(srcn[srcn.index('pi = {"pi2"'):srcn.index('print("   pi are fixed')])
g3, g4 = G["(3)"], G["(4)"]
rho43 = tuple(x @ y for x, y in zip(g4, g3)); rho34 = tuple(x @ y for x, y in zip(g3, g4))
DG = iso(pts["202"], *g4)
exact = lambda A, B: len(keys(A).keys() & keys(B).keys())
print("printed rho equals (3)(4) as a matrix product:", all(np.array_equal(a, b) for a, b in zip(rho34, G["rho"])), "; equals (4)(3):", all(np.array_equal(a, b) for a, b in zip(rho43, G["rho"])))
print("rho' = (4)(3) on 204 vs (4) on 202:", exact(iso(pts["204"], *rho43), DG), "/48; printed rho on 204 vs (4) on 202:", exact(iso(pts["204"], *G["rho"]), DG), "/48")
print("rho' V =", rho43[1].astype(int).tolist(), "; U x W^-T a signed permutation:", signed_perm(np.kron(rho43[0], np.linalg.inv(rho43[2]).T)))
print("== canonical rows (L, R, P columns), nonzeros, amp, gamma_inf,2 ==")
for n, S in (("204", pts["204"]), ("203", pts["203"]), ("202", pts["202"]), ("(4)202", DG), ("201", pts["201"])):
    L, Rr, P = arrays(S)
    can = [sum(1 for t in S if (np.abs(t[j]) > 1e-9).sum() == 1) for j in range(3)]
    nz = [int((np.abs(M) > 1e-9).sum()) for M in (L, Rr, P)]
    w = np.linalg.norm(L, axis=1) * np.linalg.norm(Rr, axis=1)
    print(f"   {n:7s} canonical {can}  nonzeros {nz}  amp {(0.5 * np.sqrt((P ** 2) @ (w ** 2))).max():.3f}  gamma {(np.abs(P) @ w).max():.3f}")
print("== P at Ruchit's point against P of the 203 files ==")
P2, P3 = arrays(pts["202"])[2], arrays(pts["203"])[2]
print("   same rows, columns equal up to sign and order:", Counter(map(nkey, P2.T)) == Counter(map(nkey, P3.T)))
c2 = {nkey(P2[:, k]): k for k in range(48)}
sub = {}
for j in range(48):
    k = c2[nkey(P3[:, j])]; s = 1 if np.allclose(P3[:, j], P2[:, k]) else -1
    assert np.allclose(P3[:, j], s * P2[:, k]); sub[j] = (k, s)
out = []
for line in open(f"{f203}/4x4x4_48_203_P.slp"):
    m = re.match(r"^\s*([a-z]\w*):=(.*);\s*$", line)
    if not m: out.append(line); continue
    lhs, rhs = m.group(1), m.group(2).replace(" ", "")
    terms = re.findall(r"([+-]?)([ito]\d+)", rhs)
    assert "".join(a + b for a, b in terms) == rhs, line
    new = ""
    for sg, tok in terms:
        s = -1 if sg == "-" else 1
        if tok[0] == "i": k, t = sub[int(tok[1:])]; tok = f"i{k}"; s *= t
        new += ("-" if s < 0 else ("+" if new else "")) + tok
    out.append(f"{lhs}:={new};\n")
open(sys.argv[5], "w").writelines(out); print("   wrote the transported program:", sys.argv[5].split('/')[-1], len(out), "lines")
print("== the printed pi against each file's product numbering ==")
def perm_of(g, S):
    im, k0 = keys(iso(S, *g)), keys(S)
    return {im[k] + 1: k0[k] + 1 for k in im.keys() & k0.keys()}
def pk(S): return {(nrm(t[0])[0], nrm(t[1])[0], nrm(t[2])[0]): i for i, t in enumerate(S)}
d = maps(DG, pts["201"])[0]
kd = pk(DG); k1 = pk(iso(pts["201"], np.linalg.inv(d[0]), np.linalg.inv(d[1]), np.linalg.inv(d[2])))
to201 = {i + 1: k1[k] + 1 for k, i in kd.items()}
k204 = pk(iso(pts["204"], *rho43)); to204 = {i + 1: k204[k] + 1 for k, i in kd.items()}
numberings = {"202 file": {i: i for i in range(1, 49)}, "204 file": to204, "201 file": to201}
for g in ("g2", "g13", "g14"):
    q = perm_of(ST[g], DG); res = {}
    for name, m in numberings.items():
        qm = {m[i]: m[j] for i, j in q.items()}
        res[name] = [n for n, p in perm.items() if all(p[i] == qm[i] for i in p)]
    print(f"   {g:4s} moves {sum(1 for i in q if q[i] != i)} products; printed pi by numbering: {res}")
