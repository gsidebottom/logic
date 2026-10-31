import json, sys
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
sys.path.insert(0, '/Users/greg/projects/logic/matmul/dps48/rfc2610')
from collections import Counter
from fractions import Fraction as Fr
import numpy as np, gamma_fixed as GF
SP = sys.argv[1]
def per(T):
    L = T[0].reshape(48, 16); R = T[1].reshape(48, 16); P = T[2].transpose(0, 2, 1).reshape(48, 16).T
    w = np.linalg.norm(L, axis=1) * np.linalg.norm(R, axis=1)
    return (np.abs(P) @ w), .5 * np.sqrt((P ** 2) @ (w ** 2))
a = GF.load(f"{SP}/plinopt_main/data/4x4x4_48_accurate_262")
g, am = per(a)
print(f"accurate_262: per-output gamma_inf,2 values {sorted(set(np.round(g, 3).tolist()))}; per-output amp values {sorted(set(np.round(am, 3).tolist()))}")
el = json.load(open(f"{SP}/td/stab/a262.json"))
M = lambda m: np.array([[float(Fr(x)) for x in r] for r in m])
pts = [e for e in el if e['mono'][0] and e['mono'][2]]
print(f"elements signed-permutation on P's two modes at 262: {len(pts)} (id slot {sum(e['slot'] == 'id' for e in pts)})")
# orbits on the 16 output positions: position (p, q) of W under Z W X^-1 (id) or Z W^T X^-1 (slot)
par = list(range(16))
def find(i):
    while par[i] != i: par[i] = par[par[i]]; i = par[i]
    return i
for e in pts:
    X, Z = M(e['X']), M(e['Z'])
    Xi = np.linalg.inv(X)
    for p in range(4):
        for q in range(4):
            E = np.zeros((4, 4)); E[p, q] = 1
            I = Z @ (E if e['slot'] == 'id' else E.T) @ Xi
            r, s = [int(v[0]) for v in np.nonzero(I)]
            par[find(p * 4 + q)] = find(r * 4 + s)
print("orbits of that group on the 16 outputs:", sorted(Counter(find(i) for i in range(16)).values(), reverse=True))
print("the 24 dyadic points: gamma_inf,2 / amp / distinct per-output values of each:")
rows = Counter()
for r in json.load(open(f"{SP}/td/stab/../perfect/score.json")):
    g, am = per(GF.load(f"{SP}/td/perfect/{r['tag']}"))
    rows[(round(float(g.max()), 3), round(float(am.max()), 3), len(set(np.round(g, 3).tolist())), len(set(np.round(am, 3).tolist())))] += 1
for k, v in sorted(rows.items()): print(f"   gamma_inf,2 {k[0]:7.3f}  amp {k[1]:.3f}  distinct output values {k[2]}, {k[3]}  points {v}")
