#!/usr/bin/env python3
"""seed.py LANE ROUND LO HI: plain copies of the certified schemes in exact/ whose largest dimension is in
[LO, HI] and that are the best of their shape, into lanes/LANE/sources/rROUND; best.txt gets a line per shape."""
import gzip, os, re, shutil, sys
here = os.path.dirname(os.path.abspath(__file__))
lane, rnd, lo, hi = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
best = {}
for f in os.listdir(os.path.join(here, 'exact')):
    mt = re.fullmatch(r'(\d+)x(\d+)x(\d+)_m(\d+)_Q\.json\.gz', f)
    if not mt: continue
    shape, m = tuple(map(int, mt.groups()[:3])), int(mt.group(4))
    if shape not in best or m < best[shape][0]: best[shape] = (m, f)
dst = os.path.join(here, 'lanes', lane, 'sources', 'r%d' % rnd)
os.makedirs(dst, exist_ok=True)
have = set(open(os.path.join(here, 'best.txt')).read().split('\n')) if os.path.exists(os.path.join(here, 'best.txt')) else set()
with open(os.path.join(here, 'best.txt'), 'a') as bt:
    for shape, (m, f) in sorted(best.items()):
        line = '%dx%dx%d %d' % (*shape, m)
        if line not in have: bt.write(line + '\n')
        if lo <= shape[2] <= hi:
            with gzip.open(os.path.join(here, 'exact', f), 'rb') as a, open(os.path.join(dst, f[:-3]), 'wb') as b:
                shutil.copyfileobj(a, b)
            print('seeded', f[:-3])
