#!/usr/bin/env python3
"""final_list.py TABLE.json OUT.json: every format for which a scheme certified here is below the published table.

Certified schemes, by kind:
  lita   ../2026-11-20_lita/exact/        deletions + 2-reduction from LITA's squares
  proj   ../../kron_reduced/              the same from the catalog schemes (the earlier records)
  prod   built/                           serendipitous products (Smith, Sedoglavic, Perminov), built here
  del    reduce/exact/                    one deletion + 2-reduction from a product scheme

The bar is the table closed under sub-format, split and Kronecker product.  A format is PRIMARY when its
certified rank is below the bar and below everything the three operations give from the other formats (table
and ours together); otherwise it is implied by other rows and listed as such."""
import json, os, re, sys, itertools
N = 32
here = os.path.dirname(os.path.abspath(__file__))
tab = {tuple(e['format']): e['rank'] for e in json.load(open(sys.argv[1]))['entries']}
fmts = list(itertools.combinations_with_replacement(range(1, N + 1), 3))


def base(f):
    if f[0] == 1 and f[1] == 1: return f[2]
    if f[0] == 1: return f[1] * f[2]
    return tab.get(f)


def ops(R, f):
    """Best rank the three operations give for f from the other formats of R."""
    best = None
    def up(r):
        nonlocal best
        if r is not None and (best is None or r < best): best = r
    for i in range(3):
        g = list(f); g[i] += 1
        if g[i] <= N: up(R.get(tuple(sorted(g))))
        for c1 in range(1, f[i] // 2 + 1):
            g = list(f); h = list(f); g[i] = c1; h[i] = f[i] - c1
            r1, r2 = R.get(tuple(sorted(g))), R.get(tuple(sorted(h)))
            if r1 is not None and r2 is not None: up(r1 + r2)
    for p in set(itertools.permutations(f)):
        for a in range(1, p[0] + 1):
            if p[0] % a: continue
            for b in range(1, p[1] + 1):
                if p[1] % b: continue
                for c in range(1, p[2] + 1):
                    if p[2] % c: continue
                    g = tuple(sorted((a, b, c))); h = tuple(sorted((p[0] // a, p[1] // b, p[2] // c)))
                    if g == (1, 1, 1) or h == (1, 1, 1) or g > h: continue
                    r1, r2 = R.get(g), R.get(h)
                    if r1 is not None and r2 is not None: up(r1 * r2)
    return best


def close(R):
    ch = True
    while ch:
        ch = False
        for f in reversed(fmts):
            r = ops(R, f)
            if r is not None and (R.get(f) is None or r < R[f]): R[f] = r; ch = True
    return R


ours = {}                                             # format -> (rank, kind, file)
def add(kind, d, pat, ok=lambda stem: True):
    n = 0
    for fn in sorted(os.listdir(d)):
        mt = re.fullmatch(pat, fn)
        if not mt or not ok(fn): continue
        f = tuple(sorted(map(int, mt.groups()[:3]))); m = int(mt.group(4)); n += 1
        if f not in ours or m < ours[f][0]: ours[f] = (m, kind, os.path.join(os.path.relpath(d, here), fn))
    print('%-5s %4d certified files' % (kind, n))

L = os.path.join(here, '..', '2026-11-20_lita', 'exact')
add('lita', L, r'(\d+)x(\d+)x(\d+)_m(\d+)_Q\.json\.gz',
    lambda fn: 'VERIFIES EXACTLY' in open(os.path.join(L, fn[:-len('_Q.json.gz')] + '.log')).read())
add('proj', os.path.join(here, '..', '..', 'kron_reduced'), r'(\d+)x(\d+)x(\d+)_m(\d+)_Q\.json\.gz')
add('prod', os.path.join(here, 'built'), r'(\d+)x(\d+)x(\d+)_m(\d+)\.json\.gz')
good = set()
vp = os.path.join(here, 'reduce', 'verified.txt')
if os.path.exists(vp):
    for line in open(vp):
        if ' exit 0:' in line and 'VERIFIES EXACTLY' in line: good.add(line.split()[0])
add('del', os.path.join(here, 'reduce', 'exact'), r'(\d+)x(\d+)x(\d+)_m(\d+)_\w+\.json\.gz', lambda fn: fn[:-len('.json.gz')] in good)
D336 = os.path.join(here, '..', '2026-11-21_336', 'exact')      # deletions from the <9,18,18:1600> products
if os.path.isdir(D336):
    add('del', D336, r'(\d+)x(\d+)x(\d+)_m(\d+)_\w+\.json',
        lambda fn: 'VERIFIES EXACTLY' in open(os.path.join(D336, fn[:-len('.json')] + '.log')).read())

T = close({f: base(f) for f in fmts})
unclosed = [f for f in fmts if base(f) is not None and T[f] < base(f)]
print('table: %d formats, %d below their own entry after closing' % (len(tab), len(unclosed)))
R = dict(T)
for f, (m, _, _) in ours.items():
    if R.get(f) is None or m < R[f]: R[f] = m
close(R)
rows = []
for f, (m, kind, fn) in sorted(ours.items()):
    if T.get(f) is None or m >= T[f]: continue
    o = ops(R, f)
    rows.append({'format': list(f), 'rank': m, 'kind': kind, 'file': fn, 'table': tab.get(f), 'bar': T[f],
                 'gain': T[f] - m, 'primary': o is None or m < o, 'others': o})
json.dump(rows, open(sys.argv[2], 'w'), indent=0)
below_all = sum(1 for f in fmts if T.get(f) is not None and R[f] < T[f])
print('formats below the closed table with everything we hold, closed: %d (total gain %d)' % (
    below_all, sum(T[f] - R[f] for f in fmts if T.get(f) is not None)))
print('formats with a certified file below the bar: %d (gain %d); primary %d (gain %d)' % (
    len(rows), sum(r['gain'] for r in rows), sum(r['primary'] for r in rows), sum(r['gain'] for r in rows if r['primary'])))
for kind in ('lita', 'proj', 'prod', 'del'):
    k = [r for r in rows if r['kind'] == kind]; p = [r for r in k if r['primary']]
    print('  %-5s %4d formats (gain %6d), primary %4d (gain %6d), all dims <= 16: %d' % (
        kind, len(k), sum(r['gain'] for r in k), len(p), sum(r['gain'] for r in p), sum(max(r['format']) <= 16 for r in p)))
