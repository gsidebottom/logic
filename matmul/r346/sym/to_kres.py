#!/usr/bin/env python3
"""to_kres.py SCHEME OUT: a scheme (catalog .json or PLinOpt base name, as vd.load reads them) as the two inputs of the
real k-subset search: OUT.json (n, u, v, w with exact fraction strings, for kresr) and OUT.bits (every factor scaled to
a primitive integer vector and reduced mod 2, for kres8's candidate listing; kres's layout).  The bits are not a scheme
mod 2 when the scheme has even denominators: kres8 is used on them only to list the subsets whose factors or Kronecker
products are dependent, which does not depend on the scaling of the products."""
import sys, json, math
from fractions import Fraction
sys.path.insert(0, '/Users/greg/projects/logic/matmul/vdescent')
from vd import load
g, U, V, W = load(sys.argv[1])
def fr(x):
    q = Fraction(float(x)).limit_denominator(4096); assert abs(float(q) - x) < 1e-12; return q
mats = [[[fr(x) for x in row] for row in M] for M in (U, V, W)]
json.dump({'n': list(g), 'u': [[str(q) for q in r] for r in mats[0]], 'v': [[str(q) for q in r] for r in mats[1]],
           'w': [[str(q) for q in r] for r in mats[2]]}, open(sys.argv[2] + '.json', 'w'))
def prim(row):
    l = math.lcm(*[q.denominator for q in row]); z = [int(q * l) for q in row]; d = math.gcd(*z); return [abs(x // d) % 2 for x in z]
bits = ''.join(''.join(map(str, prim(r))) for M in mats for r in M)
open(sys.argv[2] + '.bits', 'w').write(bits + '\n')
dens = sorted({q.denominator for M in mats for r in M for q in r})
print(f"{sys.argv[1].split('/')[-1]}: <{g[0]}x{g[1]}x{g[2]}:{len(U)}>, denominators {dens} -> {sys.argv[2]}.json, .bits")
