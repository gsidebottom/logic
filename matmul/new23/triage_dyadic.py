#!/usr/bin/env python3
"""Triage of the dyadic (true Q-scheme) majority of the storm pool.

1. exact dedupe (sorted-summand canonical string);
2. coefficient stats: denominator depth (min c-exp), max |numerator|;
3. exact Q-rank type census: per-summand sorted (rank a, rank b, rank c)
   over Q (2^exp scaling preserves rank; ranks via integer minors);
4. Q-novelty vs all locally-known Z schemes (cached DB reps, our 53,
   mm55, the 48 storm-new): a dyadic scheme whose Q-type multiset
   matches NO known scheme's multiset is Q-inequivalent to all of them
   (rank triples are de Groote invariants over any field).
   Caveat: covers the locally cached DB slice, not all 17,376 classes.
"""
import glob, os, sys
from collections import Counter
import multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, f'{ROOT}/matmul')

def rank3(v):
    """exact rank of a 3x3 integer matrix given as 9 ints (row-major)."""
    if all(x == 0 for x in v):
        return 0
    m = [v[0:3], v[3:6], v[6:9]]
    det = (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
           - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
           + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
    if det != 0:
        return 3
    for r1 in range(3):
        for r2 in range(r1+1, 3):
            for c1 in range(3):
                for c2 in range(c1+1, 3):
                    if m[r1][c1]*m[r2][c2] - m[r1][c2]*m[r2][c1] != 0:
                        return 2
    return 1

def pv(s):
    l, r = s.rsplit('], ', 1)
    return [int(x) for x in l.strip()[2:].split(',')], int(r.rstrip(') \n'))

def tm_key(S):
    return tuple(sorted(Counter(
        tuple(sorted(rank3(f[0]) for f in t)) for t in S).items()))

def dyadic_job(b):
    S = [[pv(p) for p in ln.split(' | ')] for ln in b.strip().split('\n')]
    if len(S) != 23:
        return None
    exps = [f[1] for t in S for f in t]
    if not any(e < 0 for e in exps):
        return None                       # not dyadic
    canon = tuple(sorted(tuple((tuple(f[0]), f[1]) for f in t) for t in S))
    depth = -min(exps)
    maxn = max(abs(x) for t in S for f in t for x in f[0])
    return (hash(canon), depth, maxn, tm_key(S))

def tab_multiset(path):
    from census23 import load_tab
    S = load_tab(path)
    if S is None:
        return None
    return tuple(sorted(Counter(
        tuple(sorted(rank3(list(f)) for f in t)) for t in S).items()))

if __name__ == '__main__':
    # known Q-type multisets: cached DB reps + ours
    from census23 import load_lifted, load_sms_dir
    known = set()
    tabs = glob.glob(f'{ROOT}/matmul/dbcache/**/*.tab', recursive=True)
    print(f"computing Q-multisets of {len(tabs)} cached DB reps...", flush=True)
    with mp.Pool(7) as pool:
        for tm in pool.imap_unordered(tab_multiset, tabs, chunksize=64):
            if tm:
                known.add(tm)
    for p in glob.glob(f'{ROOT}/matmul/lifted/walk-*.txt'):
        S = load_lifted(p)
        known.add(tuple(sorted(Counter(
            tuple(sorted(rank3(list(f)) for f in t)) for t in S).items())))
    S = load_sms_dir(f'{ROOT}/matmul/mm23')
    known.add(tuple(sorted(Counter(
        tuple(sorted(rank3(list(f)) for f in t)) for t in S).items())))
    txt = open(f'{ROOT}/matmul/found23q/pool23.txt').read()
    blocks = [b for b in txt.split('---\n') if b.strip()]
    for b in blocks:                       # the 48 storm-new are integer
        S = [[pv(p) for p in ln.split(' | ')] for ln in b.strip().split('\n')]
        if len(S) == 23 and all(f[1] == 0 for t in S for f in t):
            known.add(tm_key(S))
    print(f"known Q-type multisets (local catalog): {len(known)}", flush=True)

    # dyadic pool
    seen = set()
    depths = Counter(); maxns = Counter(); novel = Counter()
    kept = []
    with mp.Pool(7) as pool:
        for r in pool.imap_unordered(dyadic_job, blocks, chunksize=64):
            if r is None:
                continue
            h, depth, maxn, tm = r
            if h in seen:
                continue
            seen.add(h)
            depths[depth] += 1
            maxns[maxn if maxn < 8 else 8] += 1
            if tm not in known:
                novel[tm] += 1
    print(f"dyadic distinct: {len(seen)}", flush=True)
    print("denominator depth histogram (2^-k):", dict(sorted(depths.items())), flush=True)
    print("max|numerator| histogram (8=8+):", dict(sorted(maxns.items())), flush=True)
    print(f"Q-NOVEL vs local catalog: {sum(novel.values())} schemes "
          f"across {len(novel)} distinct type multisets", flush=True)
    for tm, c in novel.most_common(8):
        print("  ", c, "x", list(tm), flush=True)
