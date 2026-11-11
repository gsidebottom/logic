#!/usr/bin/env python3
"""Exact verification of scheme files with kron_reduce.py's two routes, a corrupted-copy control and a ring report.
usage: kron_verify.py SCHEME.json [SCHEME.json ...]      (run with numpy available)
"""
import sys, os, copy
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kron_reduce as kr

for path in sys.argv[1:]:
    name = path.split('/')[-1]
    n, F = kr.load(path); m = len(F[0])
    print(f'{name}: shape {tuple(n)}, m = {m}', flush=True)
    conv = kr.brent(n, F, 'scheme')
    vals = [sorted({x for row in F[s] for x in row}) for s in range(3)]
    integral = all(x.denominator == 1 for v in vals for x in v)
    ternary = integral and all(abs(x) <= 1 for v in vals for x in v)
    bad = copy.deepcopy(F); t = m // 3
    i = next(i for i, x in enumerate(bad[2][t]) if x); bad[2][t][i] += 1
    ctrl = kr.brent(n, bad, 'negative control: one entry changed', convs=(conv,) if conv else ('ik', 'ki'))
    ring = 'TERNARY (all coefficients in {-1, 0, 1})' if ternary else 'INTEGRAL' if integral else 'RATIONAL'
    print(f'  RESULT {name}: {m} products; {"VERIFIES EXACTLY (" + conv + ")" if conv else "DOES NOT VERIFY"}; corrupted copy {"REJECTED" if ctrl is None else "ACCEPTED (checker is broken)"}; ring: {ring}; distinct values per slot {[len(v) for v in vals]}', flush=True)
