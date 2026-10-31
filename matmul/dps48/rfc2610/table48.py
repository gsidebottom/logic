#!/usr/bin/env python3
"""Side-cost table over the line points.  L depends on (A, B), R on (B, C), P on (C, A), so with P's cost known
per class (pside.py) it is enough to price each distinct L and R once: the total of any triple is then a lookup.

Classes: every P pattern of cost <= PMAX, with A, C and the column scalings of pclasses.py, so P is exactly the
matrix that was costed.  Middle bases: every B whose four rows are row lines or whose inverse's four columns are
column lines.  For each (class, B), diagonal powers of two in B and per-product scalings between L and R only are
chosen to minimize row scalings, as vlines.py.  Identical L or R matrices (up to row order and sign) are priced once.

  table48.py PREFIX CANON_P.json PSIDE.json OUTDIR PMAX WALL
"""
import csv, hashlib, itertools, json, multiprocessing as mp, os, re, subprocess, sys, time
srcc = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/canon_enum.py').read()
srcp = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/pclasses.py').read()
pre, cj, pj, outd, PMAX, WALL = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]), float(sys.argv[6])
sys.argv = ['x', pre, '/dev/null']
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()): exec(srcc[:srcc.index('t = time.time()')])
exec(srcp[srcp.index('def inv(M):'):srcp.index('rows_out = []')])
os.makedirs(outd + "/uniq", exist_ok=True)
LNS = "/Users/greg/projects/logic/target/release/lns48"
DEEP = {"c10_n260_1": 88, "c10_n260_2": 88, "c10_n264_4": 88, "c10_n248_0": 89, "c10_n260_3": 89}
order = sorted(json.load(open(cj)), key=lambda r: (-r[0], r[1]))
rows_ = json.load(open(pj))
classes = []
for r, (cP, nz, pairs) in zip(rows_, order):
    cost = min(r["P"] + ([DEEP[r["tag"]]] if r["tag"] in DEEP else []))
    if cost <= PMAX: classes.append((r["tag"], cost, pairs[0]))
Fm = lambda M: [[Fr(x) for x in r] for r in M]
Un, Vn, Wn = Fm_all = ([Fm(m) for m in U], [Fm(m) for m in V], [Fm(m) for m in W])
pw = np.array(list(itertools.product((-1, 0, 1), repeat=4)))
def class_point(pair):
    "A, C and the column scalings exactly as pclasses.py chose them"
    z, x = pair
    sz, qx = sel["Z"][z][0], sel["X"][x][1]
    S = [col["Z"][i] for i in range(8) if (sz >> i) & 1]; Q = [row["X"][i] for i in range(8) if (qx >> i) & 1]
    Ci = [[Fr(S[j][i]) for j in range(4)] for i in range(4)]; A = [[Fr(v) for v in r] for r in Q]
    C_ = inv(Ci); Ai = inv(A)
    Wp = np.array([[[float(y) for y in r] for r in mm(mm(C_, w), Ai)] for w in Wn])
    nz_ = [np.abs(w) > 1e-9 for w in Wp]; lg = [np.where(np.abs(w) > 1e-9, np.log2(np.abs(w) + 1e-30), 0.0) for w in Wp]
    best = None
    for dc in pw:
        for da in pw:
            nu = 0
            for w, l, m in zip(Wp, lg, nz_):
                e = (l + dc[:, None] - da[None, :])[m]
                v, c = np.unique(np.round(e, 6), return_counts=True); nu += e.size - c.max()
            if best is None or nu < best[0]: best = (nu, dc.copy(), da.copy())
    _, dc, da = best
    Dc = [[Fr(2) ** int(dc[i]) if i == j else Fr(0) for j in range(4)] for i in range(4)]; Da = [[Fr(2) ** int(da[i]) if i == j else Fr(0) for j in range(4)] for i in range(4)]
    A2 = mm(Da, A); C2 = mm(Dc, C_); A2i = inv(A2); C2i = inv(C2)
    Us = [mm(A2, u) for u in Un]; Vs = [mm(v, C2i) for v in Vn]; Ws = [mm(mm(C2, w), A2i) for w in Wn]
    for k in range(48):
        m_ = Counter(abs(y) for r in Ws[k] for y in r if y).most_common(1)[0][0]
        Ws[k] = [[y / m_ for y in r] for r in Ws[k]]; Us[k] = [[y * m_ for y in r] for r in Us[k]]
    return Us, Vs, Ws
ind = lambda vs: np.linalg.matrix_rank(np.array(vs, float)) == 4
bases = []
for c in itertools.combinations(row["Y"], 4):
    if ind(c): bases.append([[Fr(x) for x in r] for r in c])
for c in itertools.combinations(col["Y"], 4):
    if ind(c): bases.append(inv([[Fr(c[j][i]) for j in range(4)] for i in range(4)]))
TS = [2.0 ** e for e in range(-3, 4)]
pd = list(itertools.product((-1, 0, 1), repeat=3))
def rowcost(M, t):
    a = np.round(np.abs(M[np.abs(M) > 1e-9]) * t, 6)
    return 1000 * len(set(a.tolist()) - {1.0}) + int((a != 1).sum())
def text(Rows):
    return "\n".join(f"{i + 1} {j + 1} {x}" for i, r in enumerate(Rows) for j, x in enumerate(r) if x)
def canon(Ms):
    rows = []
    for m in Ms:
        v = [y for r in m for y in r]
        f = next(x for x in v if x)
        rows.append([x if f > 0 else -x for x in v])
    rows.sort(key=lambda r: [str(x) for x in r])
    return rows
def one(job):
    ci, bi, Us, Vs = job
    B = bases[bi]; bf = np.array([[float(x) for x in r] for r in B]); bif = np.linalg.inv(bf)
    Uf = np.array([[[float(y) for y in r] for r in m] for m in Us]); Vf = np.array([[[float(y) for y in r] for r in m] for m in Vs])
    best = None
    for d in pd:
        Dv = 2.0 ** np.array((0,) + d)
        Up = Uf @ bif / Dv; Vp = Dv[None, :, None] * (bf @ Vf)
        sc = sum(min(rowcost(u, t) + rowcost(v, 1 / t) for t in TS) for u, v in zip(Up, Vp))
        if best is None or sc < best[0]: best = (sc, d)
    d = best[1]
    Dm = [[(Fr(2) ** ((0,) + d)[i]) if i == j else Fr(0) for j in range(4)] for i in range(4)]
    B2 = mm(Dm, B); B2i = inv(B2)
    Ua = [mm(u, B2i) for u in Us]; Va = [mm(B2, v) for v in Vs]
    for k in range(48):
        uf = np.array([[float(y) for y in r] for r in Ua[k]]); vf = np.array([[float(y) for y in r] for r in Va[k]])
        t = Fr(min(TS, key=lambda t: rowcost(uf, t) + rowcost(vf, 1 / t))).limit_denominator(64)
        Ua[k] = [[y * t for y in r] for r in Ua[k]]; Va[k] = [[y / t for y in r] for r in Va[k]]
    rl, rr = canon(Ua), canon(Va)
    tl, tr = text(rl), text(rr)
    kl, kr = hashlib.md5(tl.encode()).hexdigest()[:16], hashlib.md5(tr.encode()).hexdigest()[:16]
    cl = sum(1 for r in rl if sum(1 for x in r if x) == 1); cr = sum(1 for r in rr if sum(1 for x in r if x) == 1)
    for k_, t_ in ((kl, tl), (kr, tr)):
        p = f"{outd}/uniq/{k_}.sms"
        if not os.path.exists(p):
            with open(p + f".{os.getpid()}", "w") as f: f.write("48 16 R\n" + t_ + "\n0 0 0\n")
            os.replace(p + f".{os.getpid()}", p)
    return ci, bi, kl, kr, cl, cr, list(d)
def price(k):
    out = f"{outd}/lns/{k}"; os.makedirs(out, exist_ok=True)
    r = subprocess.run([LNS, "--sms", f"{outd}/uniq/{k}.sms", "--out", out, "--wall", str(WALL), "--seeds", "1", "--seed", "1", "--log", "1e9"], capture_output=True, text=True, timeout=WALL + 120)
    m = re.search(r"final: best (\d+)", r.stdout + r.stderr)
    return k, int(m.group(1)) if m else None
if __name__ == "__main__":
    t0 = time.time()
    print(f"{len(classes)} classes, {len(bases)} candidate bases", flush=True)
    res = []; pts = []
    with mp.get_context("fork").Pool(12) as pool:
        for ci, (tag, cost, pair) in enumerate(classes):
            Us, Vs, Ws = class_point(pair); pts.append((Us, Vs, Ws))
            res += pool.map(one, [(ci, bi, Us, Vs) for bi in range(len(bases))], chunksize=4)
            print(f"  class {tag} P {cost}: built, {time.time() - t0:.0f} s", flush=True)
        keys = sorted({r[2] for r in res} | {r[3] for r in res})
        print(f"{len(res)} (class, B) pairs, {len({r[2] for r in res})} distinct L, {len({r[3] for r in res})} distinct R, {len(keys)} matrices to price at {WALL} s", flush=True)
        json.dump(dict(classes=classes, res=res), open(f"{outd}/pairs.json", "w"))
        cost_ = {}
        for i, (k, c) in enumerate(pool.imap_unordered(price, keys)):
            cost_[k] = c
            if i % 240 == 0: print(f"  priced {i}/{len(keys)}, {time.time() - t0:.0f} s", flush=True)
    json.dump(cost_, open(f"{outd}/cost.json", "w"))
    rows = []
    for ci, bi, kl, kr, cl, cr, d in res:
        tag, p, _ = classes[ci]
        if cost_.get(kl) and cost_.get(kr): rows.append((cost_[kl] + cost_[kr] + p, cost_[kl], cost_[kr], p, cl, cr, tag, bi))
    rows.sort()
    print("best triples:")
    for r in rows[:16]: print(f"  {r[0]}  L {r[1]} R {r[2]} P {r[3]}  canonical L,R {r[4]},{r[5]}  {r[6]} B{r[7]}")
    print("per class, best total, best L alone, best R alone:")
    for ci, (tag, p, _) in enumerate(classes):
        v = [r for r in rows if r[6] == tag]
        print(f"  {tag:14s} P {p}: total {min(r[0] for r in v)}, min L {min(r[1] for r in v)}, min R {min(r[2] for r in v)}, min L + min R + P {min(r[1] for r in v) + min(r[2] for r in v) + p}")
    print(f"# done {time.time() - t0:.0f} s")
