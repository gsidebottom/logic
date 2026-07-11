#!/usr/bin/env python3
"""Save the Q-novel dyadic schemes (triage_dyadic's novel set) to
qnovel_dyadic.txt in the resume/pool block format."""
import glob, os, sys
from collections import Counter
import multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, f'{ROOT}/matmul')
sys.path.insert(0, HERE)
from triage_dyadic import pv, tm_key, rank3, tab_multiset

if __name__ == '__main__':
    from census23 import load_lifted, load_sms_dir
    known = set()
    tabs = glob.glob(f'{ROOT}/matmul/dbcache/**/*.tab', recursive=True)
    print(f"catalog: {len(tabs)} cached DB reps...", flush=True)
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
    for b in blocks:
        S = [[pv(p) for p in ln.split(' | ')] for ln in b.strip().split('\n')]
        if len(S) == 23 and all(f[1] == 0 for t in S for f in t):
            known.add(tm_key(S))
    print(f"known multisets: {len(known)}", flush=True)

    seen = set()
    saved = 0
    with open(f'{HERE}/qnovel_dyadic.txt', 'w') as out:
        for b in blocks:
            S = [[pv(p) for p in ln.split(' | ')]
                 for ln in b.strip().split('\n')]
            if len(S) != 23:
                continue
            if not any(f[1] < 0 for t in S for f in t):
                continue
            canon = tuple(sorted(tuple((tuple(f[0]), f[1]) for f in t)
                                 for t in S))
            h = hash(canon)
            if h in seen:
                continue
            seen.add(h)
            if tm_key(S) not in known:
                out.write(b + '---\n')
                saved += 1
    print(f"saved {saved} Q-novel dyadic schemes", flush=True)
