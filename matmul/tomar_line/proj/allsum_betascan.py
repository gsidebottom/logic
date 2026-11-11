#!/usr/bin/env python3
"""beta scan: for a scheme whose all-sum in direction d is rank one (x (x) y), every vector beta gives the scheme
(Prior art: the move is the block flip of LITA -- K. Khoruzhii, L. Serafin, P. Gelss, S. Pokutta, "Local
Improvements to Trilinear Aggregation", github.com/khoruzhii/lita: a rank-one element u' (x) v' of the span of the
pair factors X_t = u_t (x) v_t replaces one of them.  "All-sum" is the case where it is the sum of all X_t.)
S_beta = {a_t (x) (b_t + beta) (x) c_t} + {x (x) beta (x) y} with one more product.  For each beta: the rank of the
Kronecker products of S_beta in the two other directions (a deficit means one more product can be dropped).
usage: allsum_betascan.py N scheme.bits LO HI   (beta in [LO, HI))"""
import sys
sys.path.insert(0, sys.path[0])
from allsum_flip import load, allsum, rank_rows

def kron(x, y, w):
    m = 0
    for i in range(w):
        if (x >> i) & 1: m |= y << (i * w)
    return m

n = int(sys.argv[1]); w = n * n
prods = load(sys.argv[2], w)
lo, hi = int(sys.argv[3]), int(sys.argv[4])
d = next(dd for dd in range(3) if rank_rows(allsum(prods, dd, w)) == 1)
rows = allsum(prods, d, w)
r, c = [(1, 2), (0, 2), (0, 1)][d]
y = next(v for v in rows if v); x = sum(1 << i for i in range(w) if rows[i])
hist = {}
for beta in range(lo, hi):
    S = []
    for p in prods:
        q = list(p); q[d] ^= beta
        if q[d]: S.append(q)
    if beta:
        q = [0, 0, 0]; q[r] = x; q[c] = y; q[d] = beta; S.append(q)
    for dd in range(3):
        if dd == d: continue
        rr, cc = [(1, 2), (0, 2), (0, 1)][dd]
        rk = rank_rows([kron(q[rr], q[cc], w) for q in S])
        key = (len(S), dd, len(S) - rk)
        hist[key] = hist.get(key, 0) + 1
        if rk < len(S) and len(S) - rk >= 1 and len(S) == 48:
            print(f'DEFICIT beta={beta} direction {dd}: {len(S)} products, rank {rk}', flush=True)
print('hist (products, direction, deficit) -> count:', sorted(hist.items()))
