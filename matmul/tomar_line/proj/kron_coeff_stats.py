#!/usr/bin/env python3
"""Coefficient statistics of catalog-convention schemes over Q: dyadic or not, and the divisions by constants.

Raw: nonzero coefficients of u, v, w (L, R, P), how many are not integers, how many have a denominator that is
not a power of two, the primes in the denominators.  Normalized: each product is rescaled so that its L and R
rows are primitive integer vectors (u_t -> lam_t u_t, v_t -> mu_t v_t, w_t -> w_t / (lam_t mu_t)); then the only
divisions left are one per output entry C[i][k] whose P row has a denominator d > 1 (compute the integer
combination, divide once by d).  Reports how many output entries need a division and by which constants.
usage: kron_coeff_stats.py SCHEME.json[.gz] ...
"""
import sys, json, gzip
from fractions import Fraction
from math import gcd

def lcm(a, b):
    return a * b // gcd(a, b)

def primes(n):
    out, p = set(), 2
    while p * p <= n:
        while n % p == 0:
            out.add(p); n //= p
        p += 1
    if n > 1: out.add(n)
    return out

def odd(n):
    while n % 2 == 0: n //= 2
    return n

for path in sys.argv[1:]:
    f = gzip.open(path, 'rt') if path.endswith('.gz') else open(path)
    d = json.load(f); n0, n1, n2 = d['n']; m = d['m']
    fr = lambda rows: [[Fraction(x) for x in row] for row in rows]
    U, V, W = fr(d['u']), fr(d['v']), fr(d['w'])
    name = path.split('/')[-1]
    line = [f'{name}: <{n0}x{n1}x{n2}:{m}>']
    ps = set(); maxden = 1
    for lab, M in (('L', U), ('R', V), ('P', W)):
        nz = [c for r in M for c in r if c]
        frac = [c for c in nz if c.denominator != 1]
        nondy = [c for c in frac if odd(c.denominator) != 1]
        for c in frac: ps |= primes(c.denominator); maxden = max(maxden, c.denominator)
        line.append(f'{lab} {len(nz)} nonzeros, {len(frac)} fractions ({len(nondy)} non-dyadic)')
    dy = ps <= {2}
    print('; '.join(line))
    print(f'    denominators: primes {sorted(ps)}, max {maxden} -> {"DYADIC" if dy else "NOT dyadic"}')
    # normalize each product: L_t, R_t primitive integer vectors
    P = [[Fraction(0)] * m for _ in range(n0 * n2)]
    for t in range(m):
        sc = []
        for row in (U[t], V[t]):
            den = 1; num = 0
            for c in row:
                if c: den = lcm(den, c.denominator)
            for c in row:
                if c: num = gcd(num, abs(c.numerator * (den // c.denominator)))
            sc.append(Fraction(den, num))           # row * sc is a primitive integer vector
        s = sc[0] * sc[1]
        for idx, c in enumerate(W[t]):
            if c:
                k, i = divmod(idx, n0)
                P[i * n2 + k][t] = c / s
    dens = []
    for r in P:
        dr = 1
        for c in r:
            if c: dr = lcm(dr, c.denominator)
        dens.append(dr)
    need = [x for x in dens if x != 1]
    nondy = [x for x in need if odd(x) != 1]
    dist = sorted(set(need))
    pf = sorted(set().union(*[primes(x) for x in need])) if need else []
    frac_after = sum(1 for r in P for c in r if c and c.denominator != 1)
    print(f'    normalized (L, R integral): {frac_after} fractional P entries; {len(need)} of {n0 * n2} output entries '
          f'need one division ({len(nondy)} by a non-power of two); {len(dist)} distinct divisors, max {max(dens)}, '
          f'primes {pf}')
