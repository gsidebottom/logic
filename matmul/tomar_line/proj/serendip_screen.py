#!/usr/bin/env python3
"""Table-level screen of the shared-factor ("serendipitous") Kronecker product: for a scheme s1 with g products
sharing a factor in one slot and any format s2 = <a,b,c>, those g*R(s2) products of s1 (x) s2 are replaced by one
scheme of <a,b,g*c> (shared u), <g*a,b,c> (shared v) or <a,g*b,c> (shared w).
Usage: serendip_screen.py TABLE.json BUDS.json [shape=rank ...]
Prints product formats whose rank by this formula is below the closed table (table + extras, closed under
sub-format / split / product).  Arithmetic only: every line needs a construction and an exact check."""
import json, sys, itertools, subprocess, os
N = 32
tab = {tuple(e['format']): e['rank'] for e in json.load(open(sys.argv[1]))['entries']}
buds = json.load(open(sys.argv[2]))
for a in sys.argv[3:]:
    s, r = a.split('='); f = tuple(sorted(map(int, s.split('x')))); tab[f] = min(tab.get(f, 10**9), int(r))
def R(a, b, c):
    f = tuple(sorted((a, b, c)))
    if f[2] > N: return None
    if f[1] == 1: return f[2]
    if f[0] == 1: return f[1] * f[2]
    return tab.get(f)
# close under sub-format, split and product (same loop as table_closure.py, in place)
fmts = list(itertools.combinations_with_replacement(range(1, N + 1), 3))
C = {f: R(*f) for f in fmts}
g_ = lambda a, b, c: C.get(tuple(sorted((a, b, c))))
ch = True
while ch:
    ch = False
    for f in reversed(fmts):
        for i in range(3):
            h = list(f); h[i] += 1
            r = g_(*h) if h[i] <= N else None
            if r is not None and (C[f] is None or r < C[f]): C[f] = r; ch = True
    for f in fmts:
        for i in range(3):
            for c1 in range(1, f[i] // 2 + 1):
                h = list(f); k = list(f); h[i] = c1; k[i] = f[i] - c1
                r1, r2 = g_(*h), g_(*k)
                if r1 is not None and r2 is not None and (C[f] is None or r1 + r2 < C[f]): C[f] = r1 + r2; ch = True
    small = [f for f in fmts if C[f] is not None and f[2] <= N // 2 and f != (1, 1, 1)]
    for f1 in small:
        for f2 in small:
            if f1 > f2 or f1[2] * f2[0] > N: continue
            for p in set(itertools.permutations(f2)):
                h = tuple(sorted(x * y for x, y in zip(f1, p)))
                if h[2] <= N and (C[h] is None or C[f1] * C[f2] < C[h]): C[h] = C[f1] * C[f2]; ch = True
def one(item):
    path, n, m, grp = item
    out = {}
    if not isinstance(grp, list): return out
    for s2 in itertools.product(range(1, N + 1), repeat=3):
        if any(n[i] * s2[i] > N for i in range(3)) or s2 == (1, 1, 1): continue
        r2 = g_(*s2)
        if r2 is None: continue
        a, b, c = s2
        memo = {}
        def sav(slot, g):                      # best saving for g products sharing a factor in this slot
            if (slot, g) in memo: return memo[slot, g]
            bestg = [0] * (g + 1)
            for t in range(2, g + 1):
                bestg[t] = bestg[t - 1]
                for h in range(2, t + 1):
                    r3 = g_(a, b, h * c) if slot == 0 else g_(h * a, b, c) if slot == 1 else g_(a, h * b, c)
                    if r3 is not None: bestg[t] = max(bestg[t], bestg[t - h] + h * r2 - r3)
            memo[slot, g] = bestg[g]
            return bestg[g]
        if max(sav(slot, max((len(x) for x in grp[slot]), default=0)) for slot in range(3)) <= 0: continue
        # greedy disjoint choice: groups by decreasing saving, each restricted to the products still free
        cand = sorted(((sav(slot, len(x)), slot, x) for slot in range(3) for x in grp[slot]), key=lambda t: -t[0])
        used = set(); total = 0
        for s0, slot, x in cand:
            if s0 <= 0: break
            free = [i for i in x if i not in used]
            s = sav(slot, len(free))
            if s > 0: total += s; used.update(free)
        if total == 0: continue
        f = tuple(sorted(n[i] * s2[i] for i in range(3)))
        rank = m * r2 - total
        if C[f] is not None and rank < C[f] and rank < out.get(f, (10**9,))[0]:
            out[f] = (rank, C[f], tab.get(f), os.path.basename(path), s2, total)
    return out
import multiprocessing
multiprocessing.set_start_method('fork')
from multiprocessing import Pool
best = {}; nsch = sum(1 for x in buds if isinstance(x[3], list))
buds.sort(key=lambda x: -(x[2] or 0))
with Pool(10) as pool:
    for k, out in enumerate(pool.imap_unordered(one, buds, chunksize=1)):
        for f, v in out.items():
            if v[0] < best.get(f, (10**9,))[0]: best[f] = v
        if k % 200 == 0: print('progress', k, len(best), flush=True)
print('schemes with shared factors:', nsch, ' formats below the closed table:', len(best))
for f in sorted(best):
    r, c, t, p, s2, tot = best[f]
    print('%dx%dx%d' % f, 'formula', r, 'closed', c, 'table', t, '|', p, '(x) %dx%dx%d' % s2, 'saving', tot)
