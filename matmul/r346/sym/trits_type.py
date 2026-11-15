#!/usr/bin/env python3
"""trits_type.py N1 N2 N3 FILE.trits...: the type of an F3 scheme (how many summands have each triple of factor ranks
over F3) and how many factor triples, up to sign, it shares with the first file."""
import sys, collections
n = [int(x) for x in sys.argv[1:4]]; shp = [(n[0], n[1]), (n[1], n[2]), (n[0], n[2])]
def rank(d, r, c):
    M = [[int(x) for x in d[i * c:(i + 1) * c]] for i in range(r)]; k = 0
    for b in range(c):
        p = next((i for i in range(k, r) if M[i][b]), None)
        if p is None: continue
        M[k], M[p] = M[p], M[k]
        inv = M[k][b]                                    # 1/x = x in F3
        M[k] = [x * inv % 3 for x in M[k]]
        for i in range(r):
            if i != k and M[i][b]: f = M[i][b]; M[i] = [(x - f * y) % 3 for x, y in zip(M[i], M[k])]
        k += 1
    return k
def norm(d):
    lead = next(x for x in d if x != '0')
    return d if lead == '1' else d.translate(str.maketrans('12', '21'))
def load(f): return [tuple(ln.split()) for ln in open(f) if ln.strip() and not ln.startswith('#')]
first = None
for f in sys.argv[4:]:
    s = load(f)
    ty = collections.Counter(tuple(rank(x[q], *shp[q]) for q in range(3)) for x in s)
    key = {tuple(norm(d) for d in x) for x in s}
    if first is None: first = key
    print(f"{f.split('/')[-1]}: rank {len(s)}, type {dict(sorted(ty.items()))}, shares {len(first & key)} with the first")
