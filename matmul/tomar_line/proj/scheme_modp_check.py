#!/usr/bin/env python3
"""Reduce a catalog-convention scheme over Q modulo primes and run it on random matrices over F_p.

Each coefficient a/b becomes a * b^-1 mod p; if some b is divisible by p the reduction is undefined and the prime
is reported as excluded.  Otherwise the reduced scheme is run on TRIALS random pairs (A, B) over F_p and compared
with A B mod p.  (The exact check over Q already proves the Brent equations over Z[1/D], D the product of the
denominator primes, so they hold mod every other prime; this is the direct demonstration.)
usage: scheme_modp_check.py SCHEME.json[.gz] p1,p2,... [TRIALS]
"""
import sys, json, gzip, random
from fractions import Fraction

path = sys.argv[1]; primes = [int(x) for x in sys.argv[2].split(',')]
trials = int(sys.argv[3]) if len(sys.argv) > 3 else 5
d = json.load(gzip.open(path, 'rt') if path.endswith('.gz') else open(path)); n0, n1, n2 = d['n']; m = d['m']
sp = lambda rows: [[(i, Fraction(x)) for i, x in enumerate(row) if x not in (0, '0')] for row in rows]
U, V, W = sp(d['u']), sp(d['v']), sp(d['w'])
out = []
for p in primes:
    if any(c.denominator % p == 0 for M in (U, V, W) for row in M for _, c in row):
        out.append(f'p={p}: undefined (a denominator is divisible by {p})'); continue
    red = lambda M: [[(i, c.numerator * pow(c.denominator, -1, p) % p) for i, c in row] for row in M]
    u, v, w = red(U), red(V), red(W)
    rng = random.Random(p); bad = 0
    for _ in range(trials):
        A = [rng.randrange(p) for _ in range(n0 * n1)]; B = [rng.randrange(p) for _ in range(n1 * n2)]
        C = [0] * (n0 * n2)
        for ut, vt, wt in zip(u, v, w):
            x = sum(c * A[i] for i, c in ut) * sum(c * B[i] for i, c in vt) % p
            if x:
                for idx, c in wt:
                    k, i = divmod(idx, n0); C[i * n2 + k] += c * x
        for i in range(n0):
            for k in range(n2):
                if (C[i * n2 + k] - sum(A[i * n1 + j] * B[j * n2 + k] for j in range(n1))) % p: bad += 1
    out.append(f'p={p}: {"correct" if bad == 0 else f"WRONG ({bad})"}')
print(f'<{n0}x{n1}x{n2}:{m}> over F_p, {trials} random pairs each: ' + '; '.join(out))
