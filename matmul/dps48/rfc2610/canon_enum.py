#!/usr/bin/env python3
"""Exact maximum number of canonical rows over the whole isotropy orbit of a rank-48 point.

In the cyclic reading a point of the orbit is (A U B^-1, B V C^-1, C W A^-1).  A row of L is canonical
only for a rank-1 U = u v^T, and then iff u is a column of A^-1 and v a row of B; likewise R: r a column of
B^-1 and s a row of C; P: p a column of C^-1 and q a row of A.  So only finitely many lines matter, and
a choice in one mode is a pair (S, Q): S lines that are columns of the inverse, Q lines that are rows.  It
extends to a dual pair of bases iff S and Q are independent and the pairing matrix q(s) has at most one
nonzero per row and column, with |S| + |Q| - #nonzeros <= 4.

Enumerates, per mode, all maximal feasible (S, Q), then maximizes over the three modes (exact, the cycle
is closed by conditioning on mode X).  Reports the side maxima and the best joint counts.

  canon_enum.py PREFIX OUT.json
"""
import itertools, json, sys, time
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
from fractions import Fraction as Fr
from functools import reduce
from math import gcd
from collections import Counter
import numpy as np
def read_sms(p):
    rows = [l.split() for l in open(p) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = [[Fr(0)] * c for _ in range(r)]
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1][int(t[1]) - 1] = Fr(t[2])
    return M
pre, out = sys.argv[1:3]
L, R, P = (read_sms(f"{pre}_{m}.sms") for m in "LRP")
Pc = list(zip(*P))
U = [[L[k][i * 4:i * 4 + 4] for i in range(4)] for k in range(48)]
V = [[R[k][i * 4:i * 4 + 4] for i in range(4)] for k in range(48)]
W = [[[Pc[k][j * 4 + i] for j in range(4)] for i in range(4)] for k in range(48)]  # transpose of the column reshaped
def prim(v):
    d = reduce(lambda a, b: a * b // gcd(a, b), (x.denominator for x in v), 1)
    a = [int(x * d) for x in v]; g = reduce(gcd, a); a = [x // g for x in a]
    s = next(x for x in a if x); return tuple(x if s > 0 else -x for x in a)
def fact(M):
    "rank-1 factorization M = c l r^T as primitive lines, or None"
    nzr = [r for r in M if any(r)]
    cols = list(zip(*M)); nzc = [c for c in cols if any(c)]
    r0, c0 = prim(nzr[0]), prim(nzc[0])
    if any(prim(r) != r0 for r in nzr) or any(prim(c) != c0 for c in nzc): return None
    return c0, r0
prods = []
for k in range(48):
    a, b, c = fact(U[k]), fact(V[k]), fact(W[k])
    assert (a is None) == (b is None) == (c is None), f"mixed type at {k}"
    if a: prods.append(dict(k=k, u=a[0], v=a[1], r=b[0], s=b[1], p=c[0], q=c[1]))
print(f"{len(prods)} products of type [1,1,1]")
col = {"X": sorted({p['u'] for p in prods}), "Y": sorted({p['r'] for p in prods}), "Z": sorted({p['p'] for p in prods})}
row = {"X": sorted({p['q'] for p in prods}), "Y": sorted({p['v'] for p in prods}), "Z": sorted({p['s'] for p in prods})}
print("distinct lines per mode, columns of the inverse / rows:", {m: (len(col[m]), len(row[m])) for m in "XYZ"})
def rank(vs):
    A = np.array(vs, float).reshape(len(vs), -1) if vs else np.zeros((0, 4)); return np.linalg.matrix_rank(A) if len(vs) else 0
def indep(idx, lines): return rank([lines[i] for i in idx]) == len(idx)
sel = {}
for m in "XYZ":
    C_, Q_ = col[m], row[m]
    pair = np.array([[sum(a * b for a, b in zip(q, s)) for s in C_] for q in Q_], dtype=np.int64)
    ok = []
    Ss = [c for n in range(5) for c in itertools.combinations(range(len(C_)), n) if indep(c, C_)]
    Qs = [c for n in range(5) for c in itertools.combinations(range(len(Q_)), n) if indep(c, Q_)]
    for S in Ss:
        for Q in Qs:
            if len(S) + len(Q) < 1: continue
            sub = (pair[np.ix_(Q, S)] != 0).astype(int) if S and Q else np.zeros((len(Q), len(S)), int)
            if (sub.sum(0) > 1).any() or (sub.sum(1) > 1).any(): continue
            if len(S) + len(Q) - sub.sum() > 4: continue
            ok.append((S, Q))
    # keep the maximal selections only
    masks = {(sum(1 << i for i in S), sum(1 << i for i in Q)) for S, Q in ok}
    maxi = [a for a in masks if not any(b != a and (a[0] & b[0]) == a[0] and (a[1] & b[1]) == a[1] for b in masks)]
    sel[m] = maxi
    print(f"mode {m}: {len(masks)} feasible selections, {len(maxi)} maximal; sizes {sorted(Counter((bin(a).count('1'), bin(b).count('1')) for a, b in maxi).items())}")
def grid(colm, cole, rowm, rowe):
    G = np.zeros((len(col[colm]), len(row[rowm])), dtype=int)
    for p in prods: G[col[colm].index(p[cole]), row[rowm].index(p[rowe])] += 1
    return G
GL, GR, GP = grid("X", "u", "Y", "v"), grid("Y", "r", "Z", "s"), grid("Z", "p", "X", "q")
print("grids: products per (column line, row line): L entries", Counter(GL.ravel().tolist()), " R", Counter(GR.ravel().tolist()), " P", Counter(GP.ravel().tolist()))
def table(G, A, B):
    "canonical count for selections A (mask on columns of the inverse, first component) and B (mask on rows, second)"
    a = np.array([[(s >> i) & 1 for i in range(G.shape[0])] for s, _ in A]); b = np.array([[(q >> i) & 1 for i in range(G.shape[1])] for _, q in B])
    return a @ G @ b.T
LT = table(GL, sel["X"], sel["Y"]); RT = table(GR, sel["Y"], sel["Z"]); PT = table(GP, sel["Z"], sel["X"])
print(f"side maxima over the orbit: L {LT.max()}, R {RT.max()}, P {PT.max()}")
t = time.time()
best = (-1,); hist = Counter()
nx, ny, nz = len(sel["X"]), len(sel["Y"]), len(sel["Z"])
# maximize over y for each (x, z): closed form by numpy broadcasting, chunked
top = {}
for x in range(nx):
    M = (LT[x][:, None] + RT).max(axis=0) + PT[:, x]                    # per z, best total with this x
    mz = M.max()
    if mz > best[0]: best = (int(mz), x)
    # the distribution of per-side triples at the optimum is found below
print(f"maximum of L + R + P canonical over the orbit: {best[0]}   ({time.time() - t:.1f} s; {nx} x {ny} x {nz} selections)")
res = dict(lines=dict(col={m: col[m] for m in col}, row={m: row[m] for m in row}), sel=sel, best=best[0], side=[int(LT.max()), int(RT.max()), int(PT.max())])
# all achievable (c_L, c_R, c_P) with total >= best - 2
tri = Counter()
for x in range(nx):
    for y in np.flatnonzero(LT[x] >= 0):
        T_ = LT[x, y] + RT[y] + PT[:, x]
        for z in np.flatnonzero(T_ >= best[0] - 2):
            tri[(int(LT[x, y]), int(RT[y, z]), int(PT[z, x]))] += 1
print("achievable (c_L, c_R, c_P) near the maximum, with the number of selection triples:")
for k, v in sorted(tri.items(), key=lambda kv: (-sum(kv[0]), kv[0])): print(f"   {k} sum {sum(k)}: {v}")
pareto = {}
res['tri'] = [[*k, v] for k, v in tri.items()]
json.dump(res, open(out, 'w'))
