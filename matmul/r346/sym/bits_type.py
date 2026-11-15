#!/usr/bin/env python3
"""bits_type.py N1 N2 N3 FILE.bits...: the type of an F2 scheme -- how many summands have each triple of factor
ranks -- and how many summands it shares with the first file (as sets).  Schemes of different types are inequivalent."""
import sys, collections
n = [int(x) for x in sys.argv[1:4]]; sz = [n[0] * n[1], n[1] * n[2], n[0] * n[2]]; shp = [(n[0], n[1]), (n[1], n[2]), (n[0], n[2])]
def rank(bits, r, c):
    rows = [int(''.join(bits[i * c:(i + 1) * c]), 2) for i in range(r)]; k = 0
    for b in range(c):
        p = next((i for i in range(k, r) if rows[i] >> b & 1), None)
        if p is None: continue
        rows[k], rows[p] = rows[p], rows[k]
        for i in range(r):
            if i != k and rows[i] >> b & 1: rows[i] ^= rows[k]
        k += 1
    return k
def load(f):
    t = [c for c in open(f).read() if c in '01']; r = len(t) // sum(sz); off = [0, r * sz[0], r * (sz[0] + sz[1])]
    return [tuple(''.join(t[off[q] + m * sz[q]: off[q] + (m + 1) * sz[q]]) for q in range(3)) for m in range(r)]
first = None
for f in sys.argv[4:]:
    s = load(f)
    ty = collections.Counter(tuple(rank(list(x[q]), *shp[q]) for q in range(3)) for x in s)
    if first is None: first = set(s)
    print(f"{f.split('/')[-1]}: rank {len(s)}, type {dict(sorted(ty.items()))}, shares {len(first & set(s))} summands with the first")
