#!/usr/bin/env python3
"""Coordinate projections of a scheme, each bounded by its 2-reducibility (Kronecker-span) ranks.

Deleting row/column indices of the three index sets (I: rows of A, J: columns of A = rows of B, K: columns
of B) restricts a scheme for <n0, n1, n2> to a smaller shape; products with a zero factor vanish.  For every
deletion pattern of at most D indices this prints the surviving products and the three Kronecker-span ranks
(modulo one 20-bit prime: a screen, to be confirmed exactly by kron_reduce.py) and compares the bound with
the catalog's best rank for the resulting shape.
usage: kron_proj_sweep.py SCHEME.json STATUS.json OUT.csv [--del D] [--workers W] [--modes IJK]
"""
import sys, os, json, itertools, time, csv
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kron_fast as kf

G = {}

def init(path):
    os.nice(15)
    n, m, F, X = kf.load_mod(path)
    G['n'] = n; G['X'] = X

def work(dels):
    n = G['n']; X = G['X']
    keep = [[i for i in range(n[s]) if i not in dels[s]] for s in range(3)]
    Y, alive = kf.project_mod(n, X, keep)
    rk = kf.kron_ranks(Y) if len(alive) else [0, 0, 0]
    return dels, len(alive), rk

if __name__ == '__main__':
    args = sys.argv[1:]; D = 1; W = 2; modes = 'IJK'
    for flag in ('--del', '--workers', '--modes'):
        if flag in args:
            i = args.index(flag); v = args[i + 1]; del args[i:i + 2]
            if flag == '--del': D = int(v)
            elif flag == '--workers': W = int(v)
            else: modes = v
    path, status_path, out = args
    status = json.load(open(status_path))
    best = {k: v['ranks'] for k, v in status.items() if isinstance(v, dict) and 'ranks' in v}
    d = json.load(open(path)); n = tuple(d['n']); m = d['m']; del d
    slots = [(s, i) for s in range(3) if 'IJK'[s] in modes for i in range(n[s])]
    jobs = []
    for k in range(1, D + 1):
        for combo in itertools.combinations(slots, k):
            dels = tuple(frozenset(i for s, i in combo if s == t) for t in range(3))
            if any(len(dels[t]) >= n[t] for t in range(3)): continue
            jobs.append(dels)
    name = path.split('/')[-1]
    print(f'{name}: shape {n}, m = {m}; {len(jobs)} deletion patterns of at most {D} indices; {W} workers', flush=True)
    t0 = time.time(); rows = []; cands = 0
    with Pool(W, initializer=init, initargs=(path,)) as pool, open(out, 'w', newline='') as fh:
        wr = csv.writer(fh); wr.writerow(['source', 'shape', 'del_I', 'del_J', 'del_K', 'survivors', 'rk0', 'rk1', 'rk2', 'bound', 'best_Q', 'best_Z', 'best_ZT'])
        for dels, alive, rk in pool.imap_unordered(work, jobs, chunksize=1):
            dims = sorted(n[t] - len(dels[t]) for t in range(3)); key = 'x'.join(map(str, dims))
            b = best.get(key, {}); bound = min(rk); q = b.get('Q')
            tag = ''
            if q and bound < q: tag = '   <<< CANDIDATE: below the catalog Q rank'; cands += 1
            elif q and bound == q: tag = '   (ties the catalog Q rank)'
            ds = ['.'.join(map(str, sorted(x))) for x in dels]
            wr.writerow([name, key, *ds, alive, *rk, bound, q, b.get('Z'), b.get('ZT')]); fh.flush()
            print(f'{key:9} del I[{ds[0]}] J[{ds[1]}] K[{ds[2]}]: {alive} survive, ranks {rk} -> {bound}; catalog Q {q} Z {b.get("Z")} ZT {b.get("ZT")}{tag}', flush=True)
    print(f'done: {len(jobs)} patterns, {cands} candidates, {time.time() - t0:.0f} s', flush=True)
