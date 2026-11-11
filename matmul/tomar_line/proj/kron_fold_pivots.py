#!/usr/bin/env python3
"""Fold one dependency of a scheme at every possible dropped product and report the coefficient ring of each result.

A dependency sum_t mu_t (X_t (x) Y_t) = 0 between the Kronecker products of two slots lets any product j of its
support be dropped: the third-slot factor of every other product t of the support becomes Z_t - (mu_t / mu_j) Z_j.
The choice of j changes the folded coefficients, so an integral or ternary result may exist for some j only.
usage: kron_fold_pivots.py SOURCE.json DEPS.json [OUT_PREFIX]     (single-dependency deps files)
With OUT_PREFIX the best fold (ternary first, then integral with the smallest largest entry) is written.
"""
import sys, json
from fractions import Fraction
from collections import Counter

def frac(x):
    return Fraction(x) if not isinstance(x, str) else Fraction(x.replace(' ', ''))

src = json.load(open(sys.argv[1])); deps = json.load(open(sys.argv[2]))
assert len(deps['dependencies']) == 1, 'single-dependency files only'
d = deps['direction']; key = 'uvw'[d]
mu = {int(t): frac(v) for t, v in deps['dependencies'][0]['mu'].items()}
Z = [[frac(x) for x in row] for row in src[key]]
best = None
for j in sorted(mu):
    rows = {}
    for t in mu:
        if t == j: continue
        c = mu[t] / mu[j]
        rows[t] = [a - c * b for a, b in zip(Z[t], Z[j])]
    vals = Counter(x for r in rows.values() for x in r if x)
    integral = all(x.denominator == 1 for x in vals)
    big = max(abs(x) for x in vals)
    ternary = integral and big <= 1
    zero_rows = [t for t, r in rows.items() if not any(r)]
    odd = {str(x): n for x, n in vals.items() if abs(x) != 1}
    print(f'drop product {j:5}: {"TERNARY" if ternary else "integral" if integral else "rational"}; largest entry {big}; entries other than +-1: {odd}; products left with a zero factor: {zero_rows}')
    score = (0 if ternary else 1 if integral else 2, big, sum(odd.values()))
    if best is None or score < best[0]: best = (score, j, rows)
if len(sys.argv) > 3:
    score, j, rows = best
    out = {k: [list(r) for r in src[k]] for k in 'uvw'}
    for t, r in rows.items():
        out[key][t] = [int(x) if x.denominator == 1 else f'{x.numerator}/{x.denominator}' for x in r]
    keep = [t for t in range(src['m']) if t != j]
    res = {'n': src['n'], 'm': len(keep), 'z2': False, 'u': [out['u'][t] for t in keep], 'v': [out['v'][t] for t in keep], 'w': [out['w'][t] for t in keep]}
    name = f'{sys.argv[3]}_drop{j}.json'
    json.dump(res, open(name, 'w'))
    print(f'written {name}: dropped product {j}, {len(keep)} products, class {("ternary", "integral", "rational")[score[0]]}')
