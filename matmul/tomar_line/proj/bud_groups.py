#!/usr/bin/env python3
"""Shared-factor groups ("buds") of every scheme JSON under a catalog directory: for each slot (u, v, w) the sets
of products whose rows are proportional.  Reads data only.  Usage: bud_groups.py CATALOG_DIR OUT.json [procs]"""
import json, os, sys
from fractions import Fraction
from multiprocessing import Pool
def groups(rows):
    d = {}
    for i, row in enumerate(rows):
        nz = [(j, x) for j, x in enumerate(row) if x != 0 and x != '0']
        if not nz: continue
        f = Fraction(str(nz[0][1]))
        key = tuple((j, Fraction(str(x)) / f) for j, x in nz)
        d.setdefault(key, []).append(i)
    return [g for g in d.values() if len(g) > 1]
def one(path):
    try:
        s = json.load(open(path))
        if 'u' not in s or s.get('z2'): return None
        g = [groups(s[k]) for k in 'uvw']
        if not any(g): return [path, s['n'], s['m'], None]
        return [path, s['n'], s['m'], g]
    except Exception as e:
        return [path, None, None, 'ERR ' + repr(e)[:100]]
if __name__ == '__main__':
    files = sorted(os.path.join(r, f) for r, _, fs in os.walk(sys.argv[1]) for f in fs
                   if f.endswith('.json') and not f.endswith('_reduced.json'))
    with Pool(int(sys.argv[3]) if len(sys.argv) > 3 else 10) as p:
        out = [x for x in p.imap_unordered(one, files, chunksize=4) if x]
    json.dump(out, open(sys.argv[2], 'w'))
    print(len(files), 'files,', len(out), 'non-Z2 schemes,', sum(1 for x in out if isinstance(x[3], list)), 'with groups,',
          sum(1 for x in out if isinstance(x[3], str)), 'errors')
