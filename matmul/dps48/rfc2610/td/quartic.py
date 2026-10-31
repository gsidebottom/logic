# Can any orthonormal frames, not only the F4 ones, make all 64 elements signed permutations at 262?
# Maximize the sum of fourth powers over the orthogonal triple (A, B, C): an orthogonal matrix has fourth
# powers summing to at most 4, with equality iff it is a signed permutation, so the bound is 12 per element.
import json, sys, time
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
from fractions import Fraction as Fr
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize
el = json.load(open(sys.argv[1]))
M = lambda m: np.array([[float(Fr(x)) for x in r] for r in m])
norm = lambda g: g / abs(np.linalg.det(g)) ** .25
ids = [(norm(M(e['X'])), norm(M(e['Y'])), norm(M(e['Z']))) for e in el if e['slot'] == 'id']
sl = [(norm(M(e['X'])), norm(M(e['Y'])), norm(M(e['Z']))) for e in el if e['slot'] != 'id']
Xi, Yi, Zi = map(np.array, zip(*ids)); Xs, Ys, Zs = map(np.array, zip(*sl))
iu = np.triu_indices(4, 1)
def skew(x):
    S = np.zeros((4, 4)); S[iu] = x; return S - S.T
def f(x, which):
    A, B, C = expm(skew(x[:6])), expm(skew(x[6:12])), expm(skew(x[12:]))
    s = 0.0
    if which != 'slot': s += ((A @ Xi @ A.T) ** 4).sum() + ((B @ Yi @ B.T) ** 4).sum() + ((C @ Zi @ C.T) ** 4).sum()
    if which != 'id': s += ((A @ Xs @ C.T) ** 4).sum() + ((B @ Ys @ B.T) ** 4).sum() + ((C @ Zs @ A.T) ** 4).sum()
    return -s
rng = np.random.default_rng(1); t0 = time.time()
for which, bound in (('id', 12 * 32), ('all', 12 * 64)):
    best = 0; vals = []
    for r in range(40):
        if time.time() - t0 > 300: break
        res = minimize(f, rng.normal(size=18) * 2, args=(which,), method='L-BFGS-B', options=dict(maxiter=300))
        vals.append(-res.fun); best = max(best, -res.fun)
    print(f"{which}: best {best:.4f} of bound {bound}; {len(vals)} restarts; top values {sorted(set(np.round(vals, 3).tolist()), reverse=True)[:5]}", flush=True)
