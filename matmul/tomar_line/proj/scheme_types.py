#!/usr/bin/env python3
"""Sandwich-invariant 'type' of each scheme in a directory (the multiset of
(rank a_s, rank b_s, rank c_s)); compares two directories by distinct schemes
(sorted terms) and distinct types.  usage: types.py N1 N2 N3 DIR1 DIR2"""
import sys, glob, os
from collections import Counter
n1, n2, n3 = map(int, sys.argv[1:4])
def rank(bits, h, w):
    rows = [int(''.join(str(b) for b in bits[i*w:(i+1)*w]), 2) for i in range(h)]
    r = 0
    rows = [x for x in rows if x]
    while rows:
        piv = rows.pop()
        r += 1
        low = piv & -piv
        rows = [x ^ piv if x & low else x for x in rows]
        rows = [x for x in rows if x]
    return r
def load(d):
    schemes = {}
    types = Counter()
    for p in glob.glob(os.path.join(d, '*.bits')):
        b = [int(c) for c in open(p).read().split()[-1]]
        w = n1*n2 + n2*n3 + n1*n3; r = len(b) // w
        sa, sb = r*n1*n2, r*n2*n3
        terms = []
        tys = []
        for s in range(r):
            a = b[s*n1*n2:(s+1)*n1*n2]; bb = b[sa+s*n2*n3:sa+(s+1)*n2*n3]; c = b[sa+sb+s*n1*n3:sa+sb+(s+1)*n1*n3]
            terms.append((tuple(a), tuple(bb), tuple(c)))
            t3 = (rank(a, n1, n2), rank(bb, n2, n3), rank(c, n1, n3))
            tys.append(tuple(sorted(t3)) if n1 == n2 == n3 else t3)  # S3-invariant on square formats
        key = tuple(sorted(terms))
        ty = tuple(sorted(tys))
        schemes[key] = (r, ty)
        types[ty] += 1
    return schemes, types
A, tA = load(sys.argv[4]); B, tB = load(sys.argv[5])
print(f"{sys.argv[4]}: {len(A)} distinct schemes, {len(tA)} distinct types; ranks {Counter(v[0] for v in A.values())}")
print(f"{sys.argv[5]}: {len(B)} distinct schemes, {len(tB)} distinct types; ranks {Counter(v[0] for v in B.values())}")
print(f"schemes in both: {len(set(A) & set(B))}; types in both: {len(set(tA) & set(tB))}; types only in first: {len(set(tA) - set(tB))}; only in second: {len(set(tB) - set(tA))}")
