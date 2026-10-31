#!/usr/bin/env python3
"""How R^4 decomposes under the stabilizer at a gamma_2 minimum, per mode: the commutant of the
trivial-slot group, its eigenspaces, the group's image, and where the vectors of the type [1,1,1]
products lie.  In the cyclic reading (U, V, W) -> (X U Y^-1, Y V Z^-1, Z W X^-1) a product of type
[1,1,1] has U = u v^T, V = r s^T, W = p q^T, so mode X holds u and q, mode Y holds v and r, mode Z
holds s and p; at a point where the group is orthogonal primal and dual vectors live in one space.

  geometry.py PREFIX STAB.json
"""
import json, sys
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
sys.path.insert(0, '/Users/greg/projects/logic/matmul/dps48/rfc2610')
from fractions import Fraction as Fr
from collections import Counter
import numpy as np
import gamma_fixed as GF
np.set_printoptions(precision=4, suppress=True, linewidth=140)
pre, st = sys.argv[1:3]
U, V, W = GF.load(pre); el = json.load(open(st))
M = lambda m: np.array([[float(Fr(x)) for x in r] for r in m])
triv = [e for e in el if e['slot'] == 'id']
rng = np.random.default_rng(1)
def split(G):
    S = rng.normal(size=(4, 4)); S = S + S.T
    C = sum(g @ S @ g.T for g in G) / len(G)
    w, B = np.linalg.eigh(C)
    return w, B
rk1 = lambda A: np.linalg.matrix_rank(A, tol=1e-9) == 1
idx = [k for k in range(48) if rk1(U[k]) and rk1(V[k]) and rk1(W[k])]
print(f"{len(idx)} products of type [1,1,1]")
def lv(A):
    a, s, b = np.linalg.svd(A); return a[:, 0], b[0]
vec = {"X": [], "Y": [], "Z": []}
for k in idx:
    u, v = lv(U[k]); r, s = lv(V[k]); p, q = lv(W[k])
    vec["X"] += [("u", u), ("q", q)]; vec["Y"] += [("v", v), ("r", r)]; vec["Z"] += [("s", s), ("p", p)]
for n in "XYZ":
    G = [M(e[n]) / abs(np.linalg.det(M(e[n]))) ** .25 for e in triv]
    w, B = split(G)
    gaps = [i for i in range(3) if abs(w[i + 1] - w[i]) > 1e-8]
    dims = np.diff([0] + [g + 1 for g in gaps] + [4]).tolist()
    # distinct image of the group up to sign
    imgs = {tuple(np.round(g * np.sign(g.ravel()[np.abs(g.ravel()) > 1e-9][0]), 6).ravel().tolist()) for g in G}
    print(f"mode {n}: commutant eigenspaces of dimensions {dims}; image of the 32 elements modulo sign has {len(imgs)} elements")
    Pm = B[:, :dims[0]] @ B[:, :dims[0]].T
    print("   projector on the first eigenspace, in this point's coordinates:"); print(np.round(Pm, 4))
    d = {}
    for t, x in vec[n]:
        x = x * np.sign(x[np.abs(x) > 1e-9][0]); d.setdefault(tuple(np.round(x, 5).tolist()), Counter())[t] += 1
    keys = list(d); A = np.array(keys)
    gram = np.abs(A @ A.T)
    print(f"   {len(keys)} distinct [1,1,1] vectors up to sign; used as {dict(sum((c for c in d.values()), Counter()))}")
    print("   vectors:"); print(A)
    print("   |inner products|:", dict(sorted(Counter(np.round(gram[np.triu_indices(len(keys), 1)], 4).tolist()).items())))
    print("   squared length on the first eigenspace:", sorted(Counter(np.round(np.sum((A @ B[:, :dims[0]]) ** 2, axis=1), 4).tolist()).items()))
