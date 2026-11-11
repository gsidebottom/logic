#!/usr/bin/env python3
"""Exact confirmation of a Kronecker-span deficit found by kron_rank_scan.py.
(Prior art: this is the 2-reducibility test of LITA -- K. Khoruzhii, L. Serafin, P. Gelss, S. Pokutta, "Local
Improvements to Trilinear Aggregation", github.com/khoruzhii/lita, src/reduce.h -- a strict generalization of the
Kauers-Moosbauer reduction; nothing here is a new test.)
usage: kron_null.py SCHEME D
Finds the dependencies of the Kronecker products of the two slots other than D modulo 2^31 - 1 (on the Gram
matrix), lifts each to the rationals, and verifies it EXACTLY on the Kronecker products themselves.  Prints
the support of each dependency and whether its products share factors.
"""
import sys, os
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kron_rank_scan as K
import numpy as np
P = K.P

def ratrec(a, bound=1 << 15):
    """Rational reconstruction of a mod P with numerator and denominator below bound."""
    r0, r1, s0, s1 = P, a % P, 0, 1
    while r1 > bound:
        q = r0 // r1
        r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound: return None
    return Fraction(r1, s1)

def nullspace_p(G):
    m = G.shape[0]
    M = np.concatenate([G % P, np.eye(m, dtype=np.int64)], axis=1)
    row = 0
    for col in range(m):
        nz = np.nonzero(M[row:, col])[0]
        if nz.size == 0: continue
        piv = row + int(nz[0])
        if piv != row: M[[row, piv]] = M[[piv, row]]
        inv = pow(int(M[row, col]), P - 2, P)
        M[row] = (M[row] * inv) % P
        f = M[:, col].copy(); f[row] = 0
        idx = np.nonzero(f)[0]
        if idx.size: M[idx] = (M[idx] - np.outer(f[idx], M[row])) % P
        row += 1
    return [M[i, m:] for i in range(row, m)]

if __name__ == '__main__':
    path, d = sys.argv[1], int(sys.argv[2])
    n, raw = K.load(path)
    F = [K.int_rows(M)[0] for M in raw]
    m = len(F[0]); r, c = [(1, 2), (0, 2), (0, 1)][d]
    A = np.array(F[r], dtype=np.int64); B = np.array(F[c], dtype=np.int64)
    G = ((A.dot(A.T) % P) * (B.dot(B.T) % P)) % P       # symmetric, so left and right kernels agree
    ns = nullspace_p(G)
    print(f'{os.path.basename(path)}: shape {n}, m = {m}, direction {d} (slots {r}, {c}): {len(ns)} dependencies modulo P')
    for v in ns:
        v = [int(x) for x in v]
        lead = next(x for x in v if x)
        inv = pow(lead, P - 2, P)
        lam = [ratrec(x * inv % P) if x else Fraction(0) for x in v]
        if any(x is None for x in lam):
            print('  rational reconstruction FAILED'); continue
        supp = [t for t in range(m) if lam[t]]
        # exact check on the Kronecker products (integer rows; lam scaled to integers)
        den = 1
        for x in lam: den = den * x.denominator // np.gcd(den, x.denominator)
        li = [int(x * den) for x in lam]
        tot = {}
        for t in supp:
            for i, a in enumerate(F[r][t]):
                if not a: continue
                for j, b in enumerate(F[c][t]):
                    if b: tot[(i, j)] = tot.get((i, j), 0) + li[t] * a * b
        exact = all(x == 0 for x in tot.values())
        vals = sorted(set(str(lam[t]) for t in supp), key=lambda s: Fraction(s))
        shared = {s: len(supp) - len(set(K.proj_key(F[s][t]) for t in supp)) for s in (r, c, d)}
        print(f'  dependency on {len(supp)} products, EXACT over Q: {exact}; coefficients {vals[:12]}{"..." if len(vals) > 12 else ""}')
        print(f'  products {supp[:40]}{"..." if len(supp) > 40 else ""}')
        print(f'  repeated factors inside the support (slot: count): {shared}')
