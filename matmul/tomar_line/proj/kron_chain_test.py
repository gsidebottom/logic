#!/usr/bin/env python3
"""Gate of kron_chain.py on one scheme: the Brent check modulo p must accept the input and reject a copy with one
entry changed (negative control); a fold in direction 2 and one in direction 0 must leave a valid scheme; a
two-step path with a shuffled elimination order must end in a valid scheme.  Needs numpy; run from this directory.

usage: kron_chain_test.py SCHEME.json
"""
import os
sys_path_dir = os.path.dirname(os.path.abspath(__file__))
import sys, time, numpy as np
sys.path.insert(0, sys_path_dir)
import kron_chain as kc, kron_fast as kf
path = sys.argv[1]
t0 = time.time(); n, X = kc.load_scheme_mod(path); print('loaded', n, X[0].shape[0], f'{time.time() - t0:.1f} s', flush=True)
t0 = time.time(); print('Brent mod p, input: wrong entries', kc.brent_mod(n, X), f'({time.time() - t0:.1f} s)', flush=True)
bad = [x.copy() for x in X]; t = X[0].shape[0] // 3; s = int(np.flatnonzero(bad[2][t])[0]); bad[2][t, s] = (bad[2][t, s] + 1) % kc.P0
print('negative control (one entry changed): wrong entries', kc.brent_mod(n, bad), flush=True)
for d in (2, 0):
    t0 = time.time(); Y, drop, rank = kc.fold(X, d); print(f'fold direction {d}: rank {rank}, dropped {drop} ({time.time() - t0:.1f} s)', flush=True)
    print('  Brent mod p, output: wrong entries', kc.brent_mod(n, Y), '; products', Y[0].shape[0], '; ranks', kf.kron_ranks(Y), flush=True)
    zero = [int(np.count_nonzero(~y.any(axis=1))) for y in Y]; print('  products with a zero factor per slot:', zero, flush=True)
rng = np.random.default_rng(1)
Y, path2, rk = kc.run_path(X, '20', rng, log=print); print('path 20 with a shuffled order: final', Y[0].shape[0], rk, 'Brent wrong entries', kc.brent_mod(n, Y), flush=True)
