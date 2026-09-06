#!/usr/bin/env python3
"""LP-pruned substitution recursion (2026-09-05): prove rank(R) >= target for
a residual R by: concise on side A; if the side-A code bound (HiGHS LP,
exact certificate) >= target: leaf; else fold side A by every vector
e_p + lambda (p = last A-coordinate, lambda over the others) and recurse at
target - 1 (substitution lemma). Nodes at target <= PROBE_T are deferred
to the Rust probe (schemesearch3 --probe-tensor-file). Sound by
construction; memoized per (tensor, target).
usage: lp_recursion.py TARGET SHARD NSHARD  (roots from level1_residuals.txt)"""
import sys, os, functools
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lp_ladder import exact_code_bound_side, rank_basis
from code_bound import slices_side

PROBE_T = int(os.environ.get("LP_PROBE_T", "12"))

def concise_A(t, da, db, dc):
    vecs = [sum(t[a][b] << (b * dc) for b in range(db)) for a in range(da)]
    basis = rank_basis(vecs, db * dc)
    nt = [[(v >> (b * dc)) & ((1 << dc) - 1) for b in range(db)] for v in basis]
    return nt, len(basis)

def quotient_A(t, da, db, dc, v):
    phis = rank_basis([phi for phi in range(1, 1 << da) if bin(phi & v).count('1') % 2 == 0], da)
    return [[functools.reduce(lambda x, y: x ^ y, [t[a][b] for a in range(da) if phi >> a & 1], 0) for b in range(db)] for phi in phis], len(phis)

class Solver:
    def __init__(self):
        self.memo = {}
        self.deferred = []
        self.stats = Counter()
    def solve(self, t, da, db, dc, target, depth):
        t, da = concise_A(t, da, db, dc)
        key = (tuple(tuple(r) for r in t), da, target)
        if key in self.memo:
            self.stats[('memo', depth)] += 1
            return self.memo[key]
        if target <= 0:
            return 'ok'
        if da == 0:
            return 'fail'          # zero tensor cannot have positive rank
        if target <= PROBE_T or da <= 2:
            self.deferred.append((t, da, db, dc, target))
            self.stats[('deferred', depth)] += 1
            self.memo[key] = 'deferred'
            return 'deferred'
        v = exact_code_bound_side(slices_side(t, da, db, dc, 0))
        self.stats[('lp', depth)] += 1
        if v >= target:
            self.stats[('lp-leaf', depth)] += 1
            self.memo[key] = 'ok'
            return 'ok'
        p = da - 1
        result = 'ok'
        for lam in range(1 << p):
            vec = (1 << p) | lam
            q, dq = quotient_A(t, da, db, dc, vec)
            r = self.solve(q, dq, db, dc, target - 1, depth + 1)
            if r == 'fail':
                result = 'fail'
                break
            if r == 'deferred':
                result = 'deferred'
        self.stats[('expanded', depth)] += 1
        self.memo[key] = result
        return result

if __name__ == "__main__":
    target = int(sys.argv[1]); shard = int(sys.argv[2]) if len(sys.argv) > 2 else 0; nshard = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    limit = int(sys.argv[4]) if len(sys.argv) > 4 else 10**9
    out = open(f'matmul/r22/lp_rec_deferred_t{target}_p{PROBE_T}_s{shard}.txt', 'w')
    n = 0
    for i, line in enumerate(open('matmul/r22/level1_residuals.txt')):
        if i % nshard != shard:
            continue
        if n >= limit:
            break
        f = line.split(); name = f[0]
        t = [[int(f[5 + a * 9 + b], 16) for b in range(9)] for a in range(9)]
        S = Solver()
        r = S.solve(t, 9, 9, 9, target, 0)
        for j, (tt, da, db, dc, tg) in enumerate(S.deferred):
            out.write(f"{name}_d{j} {tg} {da} {db} {dc} {' '.join(f'{tt[a][b]:03x}' for a in range(da) for b in range(db))}\n")
        out.flush()
        st = dict(sorted(S.stats.items()))
        print(f"{name}: {r}; deferred {len(S.deferred)}; stats {st}", flush=True)
        n += 1
    print("done", flush=True)
