#!/usr/bin/env python3
"""Finer de Groote class invariants than the rank-triple type (scheme_types.py),
for the same-class question among rank-r schemes over F2.

For each scheme the terms are (a_s, b_s, c_s); the de Groote equivalences
(sandwiching by GL(n1,2) x GL(n2,2) x GL(n3,2), the slot symmetries S3 on a
square format, permuting the terms) preserve every rank below, so a
different value proves a different class and the same value proves nothing.

  type   multiset over terms of the sorted triple (rank a_s, rank b_s, rank c_s)
  pairs  multiset over pairs {s,t} of the sorted triple
         (rank(a_s+a_t), rank(b_s+b_t), rank(c_s+c_t))
  triples (--triples) the same over 3-sets {s,t,u}

usage: class_invariants.py N1 N2 N3 [--triples] DIR...
Prints one line per scheme (type id, pairs id, triples id) and the groups."""
import sys, glob, os
from itertools import combinations
from collections import Counter, defaultdict

args = [a for a in sys.argv[1:] if a != '--triples']
do_triples = '--triples' in sys.argv
n1, n2, n3 = map(int, args[:3])
dirs = args[3:]
square = n1 == n2 == n3

def rank_rows(rows):
    r = 0
    rows = [x for x in rows if x]
    while rows:
        piv = rows.pop()
        r += 1
        low = piv & -piv
        rows = [x ^ piv if x & low else x for x in rows]
        rows = [x for x in rows if x]
    return r

def to_rows(bits, h, w):
    return [int(''.join(str(b) for b in bits[i*w:(i+1)*w]), 2) for i in range(h)]

def load(p):
    b = [int(c) for c in open(p).read().split()[-1]]
    w = n1*n2 + n2*n3 + n1*n3
    r = len(b) // w
    assert r * w == len(b), p
    sa, sb = r*n1*n2, r*n2*n3
    terms = []
    for s in range(r):
        a = to_rows(b[s*n1*n2:(s+1)*n1*n2], n1, n2)
        bb = to_rows(b[sa+s*n2*n3:sa+(s+1)*n2*n3], n2, n3)
        c = to_rows(b[sa+sb+s*n1*n3:sa+sb+(s+1)*n1*n3], n1, n3)
        terms.append((a, bb, c))
    return terms

def srt(t):
    return tuple(sorted(t)) if square else tuple(t)

def xor_rows(*ms):
    return [x for x in map(lambda *cols: 0 if False else None, [])] if False else [
        __import__('functools').reduce(lambda u, v: u ^ v, col) for col in zip(*ms)]

def invariants(terms):
    ty = Counter(srt((rank_rows(a), rank_rows(bb), rank_rows(c))) for a, bb, c in terms)
    pairs = Counter()
    for (a1, b1, c1), (a2, b2, c2) in combinations(terms, 2):
        pairs[srt((rank_rows([x ^ y for x, y in zip(a1, a2)]),
                   rank_rows([x ^ y for x, y in zip(b1, b2)]),
                   rank_rows([x ^ y for x, y in zip(c1, c2)])))] += 1
    tri = None
    if do_triples:
        tri = Counter()
        for (a1, b1, c1), (a2, b2, c2), (a3, b3, c3) in combinations(terms, 3):
            tri[srt((rank_rows([x ^ y ^ z for x, y, z in zip(a1, a2, a3)]),
                     rank_rows([x ^ y ^ z for x, y, z in zip(b1, b2, b3)]),
                     rank_rows([x ^ y ^ z for x, y, z in zip(c1, c2, c3)])))] += 1
    key = lambda cnt: tuple(sorted(cnt.items())) if cnt is not None else None
    return key(ty), key(pairs), key(tri)

ids = [{}, {}, {}]
rows = []
for d in dirs:
    for p in sorted(glob.glob(os.path.join(d, '*.bits'))):
        terms = load(p)
        inv = invariants(terms)
        lab = []
        for k, v in enumerate(inv):
            if v is None:
                lab.append('-')
            else:
                lab.append(ids[k].setdefault(v, len(ids[k]) + 1))
        rows.append((os.path.relpath(p), len(terms), lab))
        print(f"{os.path.relpath(p)}  rank {len(terms)}  type {lab[0]}  pairs {lab[1]}  triples {lab[2]}")
groups = defaultdict(list)
for name, r, lab in rows:
    groups[tuple(lab)].append(name)
print(f"\n{len(rows)} schemes: {len(ids[0])} distinct types, {len(ids[1])} distinct pair invariants" + (f", {len(ids[2])} distinct triple invariants" if do_triples else ""))
for lab in sorted(groups):
    print(f"  (type {lab[0]}, pairs {lab[1]}, triples {lab[2]}): {len(groups[lab])}: {' '.join(groups[lab])}")
