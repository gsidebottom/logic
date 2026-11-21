#!/usr/bin/env python3
"""Closure of a rank table (Sedoglavic's fmm_sota.json) under the three free operations:
monotonicity (a sub-format costs no more), splitting one dimension (block sum) and the Kronecker product.
Usage: table_closure.py TABLE.json [shape=rank ...]   (extra records, e.g. 13x14x14=1538)
Prints every format whose closed value is below the table's, with the operation that gives it.
Table-level arithmetic only: a line here is a claim that a construction exists, not a verified scheme."""
import json, sys, itertools
N = 32
tab = {tuple(e['format']): e['rank'] for e in json.load(open(sys.argv[1]))['entries']}
extra = {}
for a in sys.argv[2:]:
    s, r = a.split('='); extra[tuple(sorted(map(int, s.split('x'))))] = int(r)
def base(f):
    f = tuple(sorted(f))
    if f[0] == 1 and f[1] == 1: return f[2]
    if f[0] == 1: return f[1] * f[2]
    return tab.get(f)
fmts = [f for f in itertools.combinations_with_replacement(range(1, N + 1), 3)]
R = {f: base(f) for f in fmts}
why = {}
for f, r in extra.items():
    if R.get(f) is None or r < R[f]: R[f] = r; why[f] = 'ours'
def get(a, b, c): return R.get(tuple(sorted((a, b, c))))
def put(f, r, w):
    if r is not None and (R[f] is None or r < R[f]): R[f] = r; why[f] = w; return True
    return False
changed = True; rounds = 0
while changed:
    changed = False; rounds += 1
    for f in reversed(fmts):                      # monotone, from the top down
        for i in range(3):
            g = list(f); g[i] += 1
            if g[i] <= N:
                r = get(*g)
                if r is not None: changed |= put(f, r, 'sub-format of %dx%dx%d' % tuple(sorted(g)))
    for f in fmts:                                # split one dimension
        for i in range(3):
            for c1 in range(1, f[i] // 2 + 1):
                g = list(f); h = list(f); g[i] = c1; h[i] = f[i] - c1
                r1, r2 = get(*g), get(*h)
                if r1 is not None and r2 is not None:
                    changed |= put(f, r1 + r2, '%dx%dx%d + %dx%dx%d' % (*sorted(g), *sorted(h)))
    small = [f for f in fmts if R[f] is not None and f[2] <= N // 2 and f != (1, 1, 1)]
    for f1 in small:                              # Kronecker product, all orientations of the second factor
        for f2 in small:
            if f1 > f2 or f1[2] * f2[0] > N: continue
            for p in set(itertools.permutations(f2)):
                g = tuple(sorted(x * y for x, y in zip(f1, p)))
                if g[2] <= N: changed |= put(g, R[f1] * R[f2], '%dx%dx%d (x) %dx%dx%d' % (*f1, *f2))
print('rounds', rounds)
out = [(f, base(f), R[f], why[f]) for f in fmts if base(f) is not None and R[f] < base(f)]
print('formats below the table:', len(out))
for f, b, r, w in out: print('%dx%dx%d' % f, b, '->', r, r - b, '|', w)
