#!/usr/bin/env python3
"""The dependency space of the Kronecker products of a scheme, looked at product by product (modulo a 20-bit prime).

For each direction d in the list: the nullity k, the products in the support of the dependency space N (k x m),
the distinct projective points among the columns of N, the sizes of the classes of parallel columns, and per
class the largest subset whose slot-d factors scale with the columns.  Products in such a subset vanish together
in one reduction, which is what kron_kill.py searches over.  Needs numpy; run from this directory.

usage: kron_null_structure.py SCHEME.json 0,2
"""
import os
sys_path_dir = os.path.dirname(os.path.abspath(__file__))
import sys, time, collections, numpy as np
sys.path.insert(0, sys_path_dir)
import kron_chain as kc, kron_fast as kf
p = kc.P0
path = sys.argv[1]; dirs = [int(x) for x in sys.argv[2].split(',')]
n, X = kc.load_scheme_mod(path); m = X[0].shape[0]; print('loaded', n, m, flush=True)
def inv(a): return pow(int(a), p - 2, p)
for d in dirs:
    r, c = kc.RC[d]
    G = np.fmod(kf.gram(X[r], p) * kf.gram(X[c], p), p)
    rank, dep, N = kc.left_null_fast(G, p)
    k = N.shape[0]; print(f'direction {d}: rank {rank}, nullity {k}, dependent rows {sorted(int(x) for x in dep)}')
    nzc = np.flatnonzero(N.any(axis=0)); print('  products in the support:', nzc.size)
    cls = collections.defaultdict(list)
    for t in nzc:
        col = N[:, t].astype(np.int64); f = int(col[np.flatnonzero(col)[0]]); key = tuple(int(x) for x in (col * inv(f)) % p)
        cls[key].append((int(t), f))
    sizes = sorted((len(v) for v in cls.values()), reverse=True)
    print('  distinct points up to scaling:', len(cls), '; class sizes (top 30):', sizes[:30], '; singletons:', sum(1 for s in sizes if s == 1))
    wts = collections.Counter(sum(1 for x in key if x) for key in cls); print('  nonzero coordinates per point (in this basis):', sorted(wts.items()))
    vals = collections.Counter(int(x) if x < p // 2 else int(x) - p for key in cls for x in key if x); print('  coordinate values (top 12):', vals.most_common(12))
    # inside each class: which members have slot-d factors proportional with the same ratio as the points?
    F = X[d]; cons = 0; groups = []
    for key, mem in cls.items():
        sub = collections.defaultdict(list)
        for t, f in mem:
            g = tuple(int(x) for x in np.mod(F[t] * inv(f), p))      # f_t / scale: equal iff consistent
            sub[g].append(t)
        best = max(len(v) for v in sub.values()); groups.append((len(mem), best))
    print('  per class (size, largest consistent subset): histogram', sorted(collections.Counter(groups).items(), reverse=True)[:25])
