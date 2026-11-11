#!/usr/bin/env python3
"""Which products to drop: the 2-reduction as a search (a screen modulo a 20-bit prime).

Prior art: 2-reducibility and the block flip are LITA's (Khoruzhii, Serafin, Gelss, Pokutta,
github.com/khoruzhii/lita), a generalisation of the Kauers-Moosbauer reducibility.  This file only asks which
of the equivalent reductions leaves the fewest products.

In direction d write the scheme as sum_t K_t (x) f_t (K_t the Kronecker product of the two other factors, f_t
the slot-d factor), and let the rows of N (k x m) span the dependencies sum_t mu_t K_t = 0.  Every matrix
F + N^T W is a scheme with the same K_t, and a product whose row is zero is gone.  A reduction with the k
pivot products J is the W that zeroes the rows J; it drops k products for every J, but OTHER rows can vanish
with them, and how many depends on J.  With n(t) the t-th column of N, the rows that vanish are a set on
which the map n(t) -> f_t is linear, so the question is a largest consistent set of linear conditions.  The
optimum is attained at a pivot set (a vertex), and one exchange step j -> t of the pivot set changes only
the rows in the support of one normalised dependency, where the rows that vanish after the step are exactly
those sharing the ratio f'_s / N'[j, s] with t.  So a step is priced by grouping one support by that ratio.

usage: kron_kill.py SCHEME.json [--first D] [--trials T] [--seed S] [--walk W] [--out PREFIX]
Each trial reduces until no direction is deficient: at every step the direction that removes most products
(--first D forces the first direction), W exchange steps allowed without a gain.  Writes PREFIX.path.json
for the best trial (direction, pivots and extra vanishing products per step, indices in the scheme AT that
step), to be repeated exactly over Q by kron_reduce.py --pivots.
"""
import sys, os, json, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kron_chain as kc, kron_fast as kf

P0 = kc.P0
_INV = None
def inv_table(p=P0):
    global _INV
    if _INV is None:
        lst = [0, 1] + [0] * (p - 2)
        for i in range(2, p): lst[i] = (p - (p // i) * lst[p % i] % p) % p
        _INV = np.array(lst, dtype=np.int64)
    return _INV

def inv_matrix(A, p=P0):
    k = A.shape[0]; M = np.concatenate([A % p, np.eye(k, dtype=np.int64)], axis=1)
    for c in range(k):
        nz = np.flatnonzero(M[c:, c])
        if nz.size == 0: return None
        i = c + int(nz[0])
        if i != c: M[[c, i]] = M[[i, c]]
        M[c] = M[c] * pow(int(M[c, c]), p - 2, p) % p
        f = M[:, c].copy(); f[c] = 0
        M = (M - np.outer(f, M[c])) % p
    return M[:, k:]

def null_space(X, d, p=P0):
    r, c = kc.RC[d]
    G = np.fmod(kf.gram(X[r], p) * kf.gram(X[c], p), p)
    rank, dep, N = kc.left_null_fast(G, p)
    return rank, N.astype(np.int64)

def start_pivots(N, F, rng, p=P0):
    """k independent products, those with most companions first: a companion of t has a parallel column of N
    and its slot-d factor in the same ratio, so it vanishes with t."""
    INV = inv_table(p); k, m = N.shape
    supp = np.flatnonzero(N.any(axis=0))
    first = np.array([N[np.flatnonzero(N[:, t])[0], t] for t in supp]); sc = INV[first]
    PT = N[:, supp].T * sc[:, None] % p; PH = F[supp] * sc[:, None] % p
    rv = rng.integers(1, p, size=(k + F.shape[1], 2))
    h = (PT @ rv[:k] + PH @ rv[k:]) % p; key = h[:, 0] * p + h[:, 1]
    uq, invx, cnt = np.unique(key, return_inverse=True, return_counts=True)
    order = sorted(range(len(supp)), key=lambda i: (-cnt[invx[i]], rng.random()))
    basis = []; J = []
    for i in order:
        v = PT[i].copy()
        for piv, b in basis:
            if v[piv]: v = (v - v[piv] * b) % p
        nz = np.flatnonzero(v)
        if nz.size == 0: continue
        v = v * int(INV[v[nz[0]]]) % p; basis.append((int(nz[0]), v)); J.append(int(supp[i]))
        if len(J) == k: break
    assert len(J) == k
    return J

def vertex_search(N, F, rng, walk=200, p=P0, J=None):
    """Exchange steps on the pivot set.  Returns pivots, the new slot-d matrix (zero rows = products gone)."""
    INV = inv_table(p); k, m = N.shape
    if J is None: J = start_pivots(N, F, rng, p)
    A = inv_matrix(N[:, J], p); assert A is not None
    Np = A @ N % p; Fp = (F - Np.T @ F[J]) % p
    rv = rng.integers(1, p, size=(F.shape[1], 2)); H = Fp @ rv % p
    score = int(np.count_nonzero(~Fp.any(axis=1))); best = (score, list(J), Fp.copy()); idle = 0; steps = 0
    while idle <= walk:
        moves = []
        for j in range(k):
            supp = np.flatnonzero(Np[j]); q = INV[Np[j, supp]]
            key = (H[supp, 0] * q % p) * p + H[supp, 1] * q % p
            uq, first, cnt = np.unique(key, return_index=True, return_counts=True)
            z = int(cnt[0]) if uq[0] == 0 else 0
            for u, f, c in zip(uq, first, cnt):
                if u and int(c) >= z: moves.append((int(c) - z, j, int(supp[f])))
        if not moves: break
        top = max(g for g, _, _ in moves)
        pick = [mv for mv in moves if mv[0] == top]
        g, j, t = pick[int(rng.integers(len(pick)))]
        if g == 0: idle += 1
        row = Np[j] * int(INV[Np[j, t]]) % p; col = Np[:, t].copy()
        Np = (Np - np.outer(col, row)) % p; Np[j] = row
        Fp = (Fp - np.outer(row, Fp[t])) % p; H = (H - np.outer(row, H[t])) % p
        J[j] = t; steps += 1
        new = int(np.count_nonzero(~Fp.any(axis=1)))
        assert new == score + g, (new, score, g)
        score = new
        if score > best[0]: best = (score, list(J), Fp.copy()); idle = 0
    score, J, Fp = best
    A = inv_matrix(N[:, J], p); Nq = A @ N % p                      # from scratch: no drift, no bookkeeping slip
    assert np.array_equal(Fp, (F - Nq.T @ F[J]) % p)
    return J, Fp, steps

def apply(X, d, Fp):
    keep = np.flatnonzero(Fp.any(axis=1))
    Y = [x[keep] for x in X]; Y[d] = Fp[keep].astype(np.float64)
    return Y, keep

def best_step(X, d, rng, walk, restarts, p=P0):
    rank, N = null_space(X, d, p); m = X[0].shape[0]
    if N.shape[0] == 0: return None
    F = X[d].astype(np.int64); out = None
    for _ in range(restarts):
        J, Fp, steps = vertex_search(N, F, rng, walk, p)
        gone = int(np.count_nonzero(~Fp.any(axis=1)))
        if out is None or gone > out['gone']: out = {'gone': gone, 'J': J, 'Fp': Fp, 'steps': steps, 'nullity': int(N.shape[0])}
    return out

def trial(n, X, rng, first=None, walk=200, restarts=2, log=None, p=P0):
    path = []
    while True:
        m = X[0].shape[0]; cands = {}
        for d in ([first] if first is not None and not path else range(3)):
            b = best_step(X, d, rng, walk, restarts, p)
            if b: cands[d] = b
        if not cands: return X, path
        d = max(cands, key=lambda d: (cands[d]['gone'], rng.random())); b = cands[d]
        Y, keep = apply(X, d, b['Fp'])
        dead = sorted(set(range(m)) - set(int(t) for t in keep) - set(b['J']))
        path.append({'m': m, 'direction': d, 'nullity': b['nullity'], 'pivots': [int(j) for j in b['J']], 'also_zero': dead, 'm_out': int(len(keep)),
                     'seen': {str(e): [cands[e]['nullity'], cands[e]['gone']] for e in cands}})
        if log: log(f'    {m} products: direction {d}, {b["nullity"]} dependencies, {b["gone"]} products gone ({b["steps"]} exchange steps); '
                    f'[nullity, gone] per direction {path[-1]["seen"]} -> {len(keep)}')
        X = Y

if __name__ == '__main__':
    args = sys.argv[1:]; opt = {'--first': None, '--trials': 1, '--seed': 1, '--walk': 200, '--out': None}
    for key in list(opt):
        if key in args:
            i = args.index(key); opt[key] = args[i + 1] if key == '--out' else int(args[i + 1]); del args[i:i + 2]
    src = args[0]; t0 = time.time()
    n, X0 = kc.load_scheme_mod(src); m0 = X0[0].shape[0]
    print(f'{os.path.basename(src)}: shape {n}, {m0} products; Brent modulo {P0}: {kc.brent_mod(n, X0)} wrong entries', flush=True)
    best = None
    for tr in range(opt['--trials']):
        rng = np.random.default_rng(opt['--seed'] * 1000 + tr); t1 = time.time()
        X, path = trial(n, [x.copy() for x in X0], rng, opt['--first'], opt['--walk'], log=print)
        m = X[0].shape[0]; bad = kc.brent_mod(n, X)
        print(f'  trial {tr}: {m0} -> {m} products by directions {"".join(str(s["direction"]) for s in path)}; Brent modulo {P0}: {bad} wrong entries ({time.time() - t1:.0f} s)', flush=True)
        assert bad == 0
        if best is None or m < best[0]:
            best = (m, path)
            if opt['--out']: json.dump({'source': os.path.basename(src), 'n': list(n), 'm_in': m0, 'm_out': m, 'prime': P0, 'steps': path}, open(opt['--out'] + '.path.json', 'w'))
    print(f'BEST {best[0]} products from {m0} ({time.time() - t0:.0f} s)', flush=True)
