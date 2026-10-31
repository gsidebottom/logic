#!/usr/bin/env python3
"""The gamma_2 minimum of a rank-48 orbit from its stabilizer alone.  DPS's convexity result makes the
minimum unique modulo orthogonal isotropies, so at the minimum every stabilizer element is orthogonal
(a stabilizer element sends a minimizer to a minimizer).  Hence the minimum is reached at A = Q^(1/2),
Q an invariant inner product, here the group average of X^T X, |det X| = 1, per mode.  When each mode
has a one-dimensional space of invariant forms, no search is needed.

  gamma_fixed.py PREFIX STAB.json       (STAB.json from stab_matrices.py on PREFIX)
"""
import json, sys
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
from fractions import Fraction as Fr
import numpy as np
from scipy.linalg import sqrtm, expm
from scipy.optimize import minimize
def read_sms(p):
    rows = [l.split() for l in open(p) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = np.zeros((r, c))
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1, int(t[1]) - 1] = float(Fr(t[2]))
    return M
def load(pre):
    L, R, P = (read_sms(f"{pre}_{m}.sms") for m in "LRP")
    return L.reshape(48, 4, 4), R.reshape(48, 4, 4), P.T.reshape(48, 4, 4).transpose(0, 2, 1)
def act(T, A, B, C):
    Ai, Bi, Ci = np.linalg.inv(A), np.linalg.inv(B), np.linalg.inv(C)
    return A @ T[0] @ Bi, B @ T[1] @ Ci, C @ T[2] @ Ai
def gamma2(T): return float((np.linalg.norm(T[0], axis=(1, 2)) * np.linalg.norm(T[1], axis=(1, 2)) * np.linalg.norm(T[2], axis=(1, 2))).sum())
def ginf(T):
    w = np.linalg.norm(T[0], axis=(1, 2)) * np.linalg.norm(T[1], axis=(1, 2))
    return float(np.abs(T[2].transpose(0, 2, 1).reshape(48, 16).T @ w * 0 + (np.abs(T[2].transpose(0, 2, 1).reshape(48, 16)).T @ w)).max())
idx = np.triu_indices(4)
def sym(x):
    S = np.zeros((4, 4)); S[idx] = x; return S + S.T - np.diag(np.diag(S))
def params(x): return tuple(expm(sym(x[i * 10:(i + 1) * 10])) for i in range(3))
def mini(T, x0=None, tol=1e-10):
    x0 = np.zeros(30) if x0 is None else x0
    r = minimize(lambda x: np.log(gamma2(act(T, *params(x)))), x0, method='L-BFGS-B', options=dict(maxiter=4000, maxfun=400000, ftol=1e-13, gtol=1e-7))
    return float(np.exp(r.fun)), r
GM = 64 * (1 + 2 ** .5)
if __name__ == "__main__":
    pre, st = sys.argv[1:3]
    T = load(pre); el = json.load(open(st))
    M = lambda m: np.array([[float(Fr(x)) for x in r] for r in m])
    triv = [e for e in el if e['slot'] == 'id']
    print(f"{pre.split('/')[-1]}: gamma_2 here {gamma2(T):.4f}, gamma_inf,2 {ginf(T):.4f}; target minimum 64(1+sqrt 2) = {GM:.4f}")
    Qs, dims, irr = [], [], []
    for n in "XYZ":
        G = [M(e[n]) / abs(np.linalg.det(M(e[n]))) ** .25 for e in triv]
        Qs.append(sum(g.T @ g for g in G) / len(G))
        B = []
        for a in range(10):
            E = sym(np.eye(10)[a]); B.append(np.concatenate([(g.T @ E @ g - E).ravel() for g in G]))
        sv = np.linalg.svd(np.array(B).T, compute_uv=False); dims.append(int((sv < 1e-9).sum()))
        # commutant dimension of the group in this mode, projectively: sum |tr g|^2 / |G|
        irr.append(round(sum(abs(np.trace(g)) ** 2 for g in G) / len(G), 4))
    print(f"   invariant quadratic forms per mode (trivial slot part, {len(triv)} elements): {dims};  mean |tr g|^2 per mode: {irr}")
    A, B, C = (np.real(sqrtm(Q)) for Q in Qs)
    Tf = act(T, A, B, C)
    print(f"   at the group-average point: gamma_2 {gamma2(Tf):.6f}, gamma_inf,2 {ginf(Tf):.4f}")
    v, r = mini(Tf)
    print(f"   after local minimization from there: gamma_2 {v:.6f} ({r.nit} iterations)")
    v0, r0 = mini(T)
    print(f"   minimization from the point itself:  gamma_2 {v0:.6f} ({r0.nit} iterations)")
