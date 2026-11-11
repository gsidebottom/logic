#!/usr/bin/env python3
"""Iterated 2-reduction modulo a 20-bit prime: the library (null vectors, folds, a Brent check).

Prior art: 2-reducibility is LITA's (Khoruzhii, Serafin, Gelss, Pokutta, github.com/khoruzhii/lita), a
generalisation of the Kauers-Moosbauer reducibility.  This file only iterates it: after a full reduction in
one direction the Kronecker products of ANOTHER pair of slots can be dependent again, and which products are
dropped decides whether they are.  Everything here is modulo P0 (a screen); kron_reduce.py --pivots repeats
a path exactly over Q.

A scheme modulo p is three float64 matrices (rows = products) holding integers in [0, p); entries a/b of the
exact scheme enter as a * b^-1 mod p, so the three matrices are one consistent scheme over F_p.
"""
import sys, os, json
from fractions import Fraction
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kron_fast as kf

P0 = kf.P0
RC = kf.RC

def load_scheme_mod(path, p=P0):
    d = json.load(open(path)); n = tuple(d['n']); m = d['m']
    X = []
    for key in ('u', 'v', 'w'):
        M = np.zeros((m, len(d[key][0])))
        for t, row in enumerate(d[key]):
            for i, x in enumerate(row):
                if x == 0 or x == '0': continue
                f = Fraction(x) if isinstance(x, str) else Fraction(int(x)) if float(x) == int(x) else Fraction(str(x))
                if f.denominator % p == 0: raise ValueError(f'denominator divisible by {p}')
                M[t, i] = f.numerator * pow(f.denominator, p - 2, p) % p
        X.append(M)
    return n, X

def left_null_fast(G, p=P0, bs=32):
    """Blocked elimination of [G | I] modulo p.  Returns rank, the dependent rows (original indices) and the
    null vectors N (one row each, N[i, dep[i]] = 1, zero on the other dependent rows): N @ G = 0 mod p."""
    m = G.shape[0]
    M = np.concatenate([np.mod(G, p), np.eye(m)], axis=1); order = np.arange(m); r = 0
    for c0 in range(0, m, bs):
        if r >= m: break
        c1 = min(m, c0 + bs); r0 = r
        Pn = M[r0:, c0:c1]; Lp = np.zeros((m - r0, c1 - c0)); k = 0
        for j in range(c1 - c0):
            if k >= m - r0: break
            nz = np.flatnonzero(Pn[k:, j])
            if nz.size == 0: continue
            i = k + int(nz[0])
            if i != k:
                M[[r0 + k, r0 + i], c0:] = M[[r0 + i, r0 + k], c0:]
                Lp[[k, i], :k] = Lp[[i, k], :k]
                order[[r0 + k, r0 + i]] = order[[r0 + i, r0 + k]]
            inv = pow(int(Pn[k, j]), p - 2, p)
            mult = np.fmod(Pn[k + 1:, j] * inv, p)
            Pn[k + 1:, j:] = np.mod(Pn[k + 1:, j:] - np.outer(mult, Pn[k, j:]), p)
            Lp[k + 1:, k] = mult
            k += 1
        if k == 0: continue
        T = M[r0:, c1:]
        for i in range(1, k):
            T[i] = np.mod(T[i] - Lp[i, :i] @ T[:i], p)
        if k < m - r0:
            T[k:] = np.mod(T[k:] - Lp[k:, :k] @ T[:k], p)
        r += k
    return r, order[r:].copy(), M[r:, m:].copy()

def fold(X, d, rng=None, p=P0):
    """One full reduction in direction d.  rng shuffles the elimination order, i.e. which products are dropped.
    Returns the new scheme, the dropped products (indices into X) and the rank found."""
    r, c = RC[d]; m = X[0].shape[0]
    G = np.fmod(kf.gram(X[r], p) * kf.gram(X[c], p), p)
    perm = rng.permutation(m) if rng is not None else np.arange(m)
    rank, dep, N = left_null_fast(G[np.ix_(perm, perm)], p)
    if rank == m: return X, [], rank
    drop = perm[dep]; Nv = np.zeros_like(N); Nv[:, perm] = N          # back to the caller's numbering
    assert all(Nv[i, drop[i]] == 1 for i in range(len(drop)))
    keep = np.setdiff1d(np.arange(m), drop)
    assert not Nv[:, drop][~np.eye(len(drop), dtype=bool)].any()
    Y = [x[keep] for x in X]
    Y[d] = np.mod(X[d][keep] - Nv[:, keep].T @ X[d][drop], p)
    return Y, sorted(int(j) for j in drop), rank

def brent_mod(n, X, p=P0):
    """The Brent equations modulo p, in full (catalog layout: u is I x J, v is J x K, w is K x I)."""
    n0, n1, n2 = n; bad = 0
    for a in range(n0 * n1):
        i, j = divmod(a, n1)
        M = np.mod((np.mod(X[0][:, a][:, None] * X[1], p)).T @ X[2], p)
        E = np.zeros_like(M)
        for k in range(n2): E[j * n2 + k, k * n0 + i] = 1
        bad += int(np.count_nonzero(M != E))
    return bad

def run_path(X, policy, rng, p=P0, log=None):
    """Reduce until no direction is deficient.  policy: 'min' (lowest rank first), 'rand' (a random deficient
    direction) or a string of digits giving the preference order, e.g. '20'.  Returns the scheme and the path."""
    path = []
    while True:
        m = X[0].shape[0]; rk = kf.kron_ranks(X, p)
        defi = [d for d in range(3) if rk[d] < m]
        if not defi: return X, path, rk
        if policy == 'min': d = min(defi, key=lambda d: rk[d])
        elif policy == 'rand': d = defi[int(rng.integers(len(defi)))]
        else: d = next((int(ch) for ch in policy if int(ch) in defi), defi[0])
        X, drop, rank = fold(X, d, rng, p)
        path.append({'m': m, 'ranks': [int(x) for x in rk], 'direction': d, 'dropped': drop})
        if log: log(f'    {m} products, ranks {rk}: direction {d} drops {len(drop)}')
