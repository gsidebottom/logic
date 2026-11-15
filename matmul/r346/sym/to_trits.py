#!/usr/bin/env python3
"""to_trits.py SCHEME OUT.trits: a scheme (catalog .json or PLinOpt base name, as vd.load reads them) reduced mod 3
for symflip3: one summand per line, the entries of its A, B, C factors as digits 0, 1, 2.  Fails if a coefficient
has a denominator divisible by 3."""
import sys
from fractions import Fraction
sys.path.insert(0, '/Users/greg/projects/logic/matmul/vdescent')
from vd import load
g, U, V, W = load(sys.argv[1])
def trit(x):
    q = Fraction(float(x)).limit_denominator(4096)
    assert abs(float(q) - x) < 1e-12 and q.denominator % 3, f'coefficient {x} has no image mod 3'
    return str(q.numerator * pow(q.denominator, -1, 3) % 3)
with open(sys.argv[2], 'w') as f:
    for t in range(U.shape[0]):
        f.write(' '.join(''.join(trit(x) for x in M[t]) for M in (U, V, W)) + '\n')
print(f"{sys.argv[1].split('/')[-1]}: <{g[0]}x{g[1]}x{g[2]}:{U.shape[0]}> -> {sys.argv[2]}")
