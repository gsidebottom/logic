#!/usr/bin/env python3
"""summary.py TABLE.json: the certified schemes of exact/ (best per shape) against Sedoglavic's table.
A line is marked 'implied' when a certified scheme of a larger format already gives the same or a lower rank
(sub-format monotonicity), so the remaining lines are the ones that carry information."""
import json, os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
tab = {tuple(e['format']): e['rank'] for e in json.load(open(sys.argv[1]))['entries']}
best = {}
for f in os.listdir(os.path.join(here, 'exact')):
    mt = re.fullmatch(r'(\d+)x(\d+)x(\d+)_m(\d+)_Q\.json\.gz', f)
    if not mt: continue
    shape, m = tuple(map(int, mt.groups()[:3])), int(mt.group(4))
    if shape not in best or m < best[shape]: best[shape] = m
ring = {}
for f in os.listdir(os.path.join(here, 'exact')):
    mt = re.fullmatch(r'(\d+x\d+x\d+)_m(\d+)\.log', f)
    if not mt: continue
    for line in open(os.path.join(here, 'exact', f)):
        g = re.search(r'denominator primes (\[[^\]]*\]) -> (\w+)', line)
        if g: ring[(mt.group(1), int(mt.group(2)))] = g.group(2) + ' ' + g.group(1)
rows = []
for shape, m in sorted(best.items()):
    t = tab.get(shape)
    dom = [s for s, r in best.items() if s != shape and all(a >= b for a, b in zip(s, shape)) and r <= m]
    rows.append((shape, m, t, None if t is None else m - t, bool(dom), ring.get(('%dx%dx%d' % shape, m), '?')))
below = [r for r in rows if r[3] is not None and r[3] < 0]
gen = [r for r in below if not r[4]]
print('certified shapes: %d; below the table: %d; of those not implied by a larger certified one: %d' % (len(rows), len(below), len(gen)))
print('%-10s %6s %6s %6s  %s' % ('shape', 'rank', 'table', 'diff', 'ring'))
for shape, m, t, d, imp, rg in rows:
    print('%-10s %6d %6s %6s  %s%s' % ('%dx%dx%d' % shape, m, t, d, rg, '  (implied)' if imp else ''))
if '--args' in sys.argv:
    print(' '.join('%dx%dx%d=%d' % (*r[0], r[1]) for r in gen))
