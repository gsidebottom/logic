#!/usr/bin/env python3
"""Fast screen for the 2-reducibility bound of a bilinear scheme and of its coordinate projections.

The bound (LITA's 2-reducibility, github.com/khoruzhii/lita): a scheme sum_t u_t (x) v_t (x) w_t needs no more
products than the dimension of the span of the Kronecker products of any two of its slots.  Here the dimension
is the rank of the Gram matrix (X X^T o Y Y^T) modulo one prime near 2^20, by a blocked elimination whose
products run in float64 BLAS (exact: every partial sum stays below 2^53).  The rank modulo p never exceeds the
rank over Q, so full rank is a certificate and a deficit is a claim that kron_reduce.py must confirm exactly.
"""
import json, math
from fractions import Fraction
import numpy as np
np.seterr(all="ignore")      # Accelerate raises spurious floating-point flags in matmul on this Mac; every product here is exact

P0 = 1048573          # the largest prime below 2^20
RC = [(1, 2), (0, 2), (0, 1)]

def frac(x):
    return Fraction(x) if not isinstance(x, str) else Fraction(x.replace(' ', ''))

def load_mod(path, p=P0):
    """n, m, and the three factor matrices modulo p as float64 (each row scaled to integers first), plus the exact rows."""
    d = json.load(open(path))
    n = tuple(d['n']); m = d['m']
    F = []; X = []
    for key in 'uvw':
        rows = [[frac(x) for x in row] for row in d[key]]
        assert len(rows) == m
        F.append(rows)
        M = np.zeros((m, len(rows[0])), dtype=np.float64)
        for t, row in enumerate(rows):
            L = 1
            for x in row:
                if x.denominator != 1: L = L * x.denominator // math.gcd(L, x.denominator)
            for i, x in enumerate(row):
                if x: M[t, i] = int(x * L) % p
        X.append(M)
    return n, m, F, X

def rank_mod(M, p=P0, bs=32):
    """Rank modulo p of a float64 matrix with entries in [0, p); destroys nothing (works on a copy)."""
    M = M.copy(); m, n = M.shape; r = 0
    for c0 in range(0, n, bs):
        if r >= m: break
        c1 = min(n, c0 + bs); r0 = r
        Pn = M[r0:, c0:c1]
        Lp = np.zeros((m - r0, c1 - c0)); k = 0
        for j in range(c1 - c0):
            if k >= m - r0: break
            nz = np.flatnonzero(Pn[k:, j])
            if nz.size == 0: continue
            i = k + int(nz[0])
            if i != k:
                M[[r0 + k, r0 + i], c0:] = M[[r0 + i, r0 + k], c0:]
                Lp[[k, i], :k] = Lp[[i, k], :k]
            inv = pow(int(Pn[k, j]), p - 2, p)
            mult = np.fmod(Pn[k + 1:, j] * inv, p)
            Pn[k + 1:, j:] = np.mod(Pn[k + 1:, j:] - np.outer(mult, Pn[k, j:]), p)
            Lp[k + 1:, k] = mult
            k += 1
        if k == 0: continue
        if c1 < n:
            T = M[r0:, c1:]
            for i in range(1, k):
                T[i] = np.mod(T[i] - Lp[i, :i] @ T[:i], p)
            if k < m - r0:
                T[k:] = np.mod(T[k:] - Lp[k:, :k] @ T[:k], p)
        r += k
    return r

def gram(X, p=P0):
    return np.fmod(X @ X.T, p)

def kron_ranks(Xs, p=P0, dirs=(0, 1, 2)):
    """Ranks of the three Kronecker spans (direction d pairs the two slots other than d)."""
    G = [gram(X, p) for X in Xs]
    out = []
    for d in dirs:
        r, c = RC[d]
        out.append(rank_mod(np.fmod(G[r] * G[c], p), p))
    return out

def cols_for(n, keep):
    """Column selections of the three slots for kept index sets (I, J, K): u is I x J, v is J x K, w is K x I."""
    n0, n1, n2 = n; I, J, K = keep
    cu = [i * n1 + j for i in I for j in J]
    cv = [j * n2 + k for j in J for k in K]
    cw = [k * n0 + i for k in K for i in I]
    return cu, cv, cw

def project_mod(n, X, keep):
    cu, cv, cw = cols_for(n, keep)
    Y = [X[0][:, cu], X[1][:, cv], X[2][:, cw]]
    alive = np.flatnonzero(Y[0].any(axis=1) & Y[1].any(axis=1) & Y[2].any(axis=1))
    return [y[alive] for y in Y], alive
