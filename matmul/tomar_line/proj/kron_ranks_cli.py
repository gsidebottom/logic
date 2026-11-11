#!/usr/bin/env python3
"""Print the three Kronecker-span ranks of schemes modulo a 20-bit prime (a screen, see kron_fast.py).

Prior art: the bound min(rank) is the 2-reducibility bound of LITA (github.com/khoruzhii/lita).

usage: kron_ranks_cli.py SCHEME.json ...
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kron_fast as kf

for path in sys.argv[1:]:
    t0 = time.time()
    n, m, F, X = kf.load_mod(path)
    rk = kf.kron_ranks(X)
    print(f'{os.path.basename(path)}: shape {"x".join(map(str, n))}, {m} products, Kronecker-span ranks {rk} -> bound {min(rk)} ({time.time() - t0:.1f} s)', flush=True)
