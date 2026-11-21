#!/usr/bin/env python3
"""Subspace grids in scheme files: sets S of products whose factors in one slot lie in a plane and whose factors
in a second slot lie in a plane, without being proportional.  The sum over S is then a tensor in C^2 (x) V (x) C^2,
an image of <1,2,2>, so S (x) <a,b,c> is an image of <a,2b,2c> (rotations for the other slot pairs): with
|S| = 4 that replaces 4 rank(a,b,c) products by rank(a,2b,2c).  Proportional factors (classes) give the grids
of serendip_plan.py; this looks for the ones that are not made of classes.
usage: subspace_grids.py BUDS.json OUT.json [MAX_RANK]   (reads the scheme files named in BUDS.json; data only)"""
import json, sys, os
from fractions import Fraction
import numpy as np
P = 2147483647


def modp(x):
    f = Fraction(str(x)); return f.numerator % P * pow(f.denominator, -1, P) % P


def norm(M):
    """Rows scaled to have 1 at their first nonzero entry (zero rows stay); returns (M, is nonzero)."""
    M = M % P
    nz = M != 0
    has = nz.any(axis=1)
    first = nz.argmax(axis=1)
    lead = M[np.arange(len(M)), first]
    inv = np.array([pow(int(v), -1, P) if h else 0 for v, h in zip(lead, has)], dtype=np.int64)
    return M * inv[:, None] % P, has


def planes(M, idx, min_dirs):
    """Sets of rows (among idx) of M lying in one plane, with at least min_dirs distinct directions."""
    sub, _ = norm(M[idx])
    out = set()
    dirs = {}
    for a, row in enumerate(sub): dirs.setdefault(row.tobytes(), []).append(a)
    reps = [v[0] for v in dirs.values()]
    for a in reps:
        piv = int((sub[a] != 0).argmax())
        res, has = norm(sub - sub[:, piv:piv + 1] * sub[a][None, :])
        groups = {}
        for b in range(len(sub)):
            if has[b]: groups.setdefault(res[b].tobytes(), []).append(b)
        same = [b for b in range(len(sub)) if not has[b]]
        for g in groups.values():
            members = same + g
            nd = len({sub[b].tobytes() for b in members})
            if nd >= min_dirs: out.add((frozenset(idx[b] for b in members), nd))
    return out


def scan(path):
    d = json.load(open(path))
    m = d['m']
    M = [np.array([[modp(x) for x in row] for row in d[k]], dtype=np.int64) for k in 'uvw']
    found = {}
    allidx = list(range(m))
    for X in range(3):
        for S, nd in planes(M[X], allidx, 3):          # a plane with at least three directions in slot X
            if len(S) < 4: continue
            for Y in range(3):
                if Y == X: continue
                for S2, nd2 in planes(M[Y], sorted(S), 2):
                    if len(S2) >= 4:
                        ndx = len({norm(M[X][[t]])[0].tobytes() for t in S2})
                        if ndx >= 3 or nd2 >= 3: found[(min(X, Y), max(X, Y), tuple(sorted(S2)))] = (ndx, nd2) if X < Y else (nd2, ndx)
    return [[a, b, list(S), list(v)] for (a, b, S), v in found.items()]


if __name__ == '__main__':
    buds = json.load(open(sys.argv[1])); cap = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    files = sorted((x[2], x[0]) for x in buds if x[2] and x[2] <= cap)
    from multiprocessing import Pool
    res = {}
    with Pool(int(os.environ.get('PROCS', '6'))) as pool:
        for (m, path), r in zip(files, pool.imap(scan, [f[1] for f in files], chunksize=4)):
            if r: res[path] = r
    json.dump(res, open(sys.argv[2], 'w'))
    sizes = {}
    for r in res.values():
        for a, b, S, v in r: sizes[len(S)] = sizes.get(len(S), 0) + 1
    print('schemes scanned: %d (rank <= %d); with a subspace grid of 4 or more products: %d; by size: %s' % (len(files), cap, len(res), sorted(sizes.items())))
