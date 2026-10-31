#!/usr/bin/env python3
"""Every middle basis fixed by [1,1,1] lines at a point whose P is kept: B with all four rows on row lines,
or B^-1 with all four columns on column lines, 140 candidates at most.  U' = U B^-1, V' = B V, W unchanged,
so P and its program stay exactly as they are.  Diagonal powers of two in B and per-product scalings between
L and R only are chosen to minimize the scalings a row needs, one per distinct magnitude other than 1.  Writes the points and a pool for sweep.py FIXED_P.

  vlines.py PREFIX OUTDIR
"""
import csv, itertools, json, os, sys
srcc = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/canon_enum.py').read()
srcp = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/pclasses.py').read()
pre, outd = sys.argv[1:3]
sys.argv = ['x', pre, '/dev/null']
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()): exec(srcc[:srcc.index('def rank(vs)')])
exec(srcp[srcp.index('def inv(M):'):srcp.index('rows_out = []')])
sys.path.insert(0, '/Users/greg/projects/logic/matmul/dps48')
import orbit48 as O
os.makedirs(outd, exist_ok=True)
ind = lambda vs: np.linalg.matrix_rank(np.array(vs, float)) == 4
bases = []
for c in itertools.combinations(row["Y"], 4):
    if ind(c): bases.append(("r", [[Fr(x) for x in r] for r in c]))
for c in itertools.combinations(col["Y"], 4):
    if ind(c): bases.append(("c", inv([[Fr(c[j][i]) for j in range(4)] for i in range(4)])))
print(len(bases), "candidate bases")
Un = np.array([[[float(x) for x in r] for r in m] for m in U]); Vn = np.array([[[float(x) for x in r] for r in m] for m in V])
pw = list(itertools.product((-1, 0, 1), repeat=3))
TS = [2.0 ** e for e in range(-3, 4)]
def rowcost(M, t):
    "a row costs one scaling per distinct magnitude other than 1; coefficients off 1 break ties"
    a = np.round(np.abs(M[np.abs(M) > 1e-9]) * t, 6)
    return 1000 * len(set(a.tolist()) - {1.0}) + int((a != 1).sum())
canL = lambda Us: sum(1 for k in range(48) if sum(1 for r in Us[k] for y in r if y) == 1)
seen = {}; rows_ = []
for bi, (kind, B) in enumerate(bases):
    bf = np.array([[float(x) for x in r] for r in B]); bif = np.linalg.inv(bf)
    best = None
    for d in pw:
        Dv = 2.0 ** np.array((0,) + d)
        Up = Un @ bif / Dv; Vp = (Dv[None, :, None] * (bf @ Vn))
        sc = 0
        for u, v in zip(Up, Vp):
            sc += min(rowcost(u, t) + rowcost(v, 1 / t) for t in TS)
        if best is None or sc < best[0]: best = (sc, d)
    sc, d = best
    Dm = [[(Fr(2) ** ((0,) + d)[i]) if i == j else Fr(0) for j in range(4)] for i in range(4)]
    B2 = mm(Dm, B); B2i = inv(B2)
    Us = [mm([[Fr(x) for x in r] for r in u], B2i) for u in U]; Vs = [mm(B2, [[Fr(x) for x in r] for r in v]) for v in V]
    for k in range(48):
        uf = np.array([[float(y) for y in r] for r in Us[k]]); vf = np.array([[float(y) for y in r] for r in Vs[k]])
        t = Fr(min(TS, key=lambda t: rowcost(uf, t) + rowcost(vf, 1 / t))).limit_denominator(64)
        Us[k] = [[y * t for y in r] for r in Us[k]]; Vs[k] = [[y / t for y in r] for r in Vs[k]]
    Ws = [[[Fr(x) for x in r] for r in w] for w in W]
    key_ = str(sorted(tuple(sorted(str(y) for r in Us[k] for y in r)) for k in range(48))) + str(sorted(tuple(sorted(str(y) for r in Vs[k] for y in r)) for k in range(48)))
    cL, cR = canL(Us), canL(Vs)
    den = lambda T_: max(Fr(y).denominator for m in T_ for r in m for y in r)
    dy = all(Fr(y).denominator & (Fr(y).denominator - 1) == 0 for T_ in (Us, Vs) for m in T_ for r in m for y in r)
    nnz = [sum(1 for m in T_ for r in m for y in r if y) for T_ in (Us, Vs)]
    mags = Counter(str(abs(y)) for T_ in (Us, Vs) for m in T_ for r in m for y in r if y)
    nons = sum(1 for T_ in (Us, Vs) for m in T_ for r in m for y in r if y and abs(y) != 1)
    if key_ in seen: seen[key_] += 1; continue
    seen[key_] = 1
    tag = f"b{bi:03d}_{cL}_{cR}"
    write(f"{outd}/{tag}", Us, Vs, Ws)
    assert brent(Us, Vs, Ws), tag
    ins = {}
    rows_.append(dict(rank=len(rows_), floor=48 - cL + 48 - cR + 38 + 32, fl=48 - cL, fr=48 - cR, fp=38, nonunit=nons, objective=0, prefix=f"{outd}/{tag}"))
    print(f"{tag:14s} {kind} canon ({cL},{cR})  nnz L,R {nnz}  non-units L+R {nons}  dyadic {int(dy)}  magnitudes {dict(mags)}", flush=True)
with open(f"{outd}/pool.csv", "w", newline="") as f:
    w_ = csv.DictWriter(f, fieldnames=list(rows_[0])); w_.writeheader(); w_.writerows(rows_)
print(len(rows_), "distinct points; canonical pairs:", sorted(Counter((48 - r['fl'], 48 - r['fr']) for r in rows_).items(), reverse=True))
