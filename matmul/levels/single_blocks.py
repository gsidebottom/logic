#!/usr/bin/env python3
"""Can an accurate scheme have operands that are single input blocks?  (2026-11-14)

A product whose left factor is one block of A needs no pass output: the GEMM reads the block in
place.  Product i's left factor is the g1 x g2 matrix X_i (row i of L), its right factor the
g2 x g3 matrix Y_i (row i of R), its output pattern the g1 x g3 matrix Z_i (column i of P).  The
symmetries of matrix multiplication act by X -> U X V^-1, Y -> V Y W^-1, Z -> U^-T Z W^T, so the
RANKS of the X_i, Y_i, Z_i are invariants of the class: only a rank-one factor can ever be a single
block, and at most g1 g2 (g2 g3) left (right) factors can be single blocks at one orbit point.
Printed: the rank profile of each scheme's factors; the single-block factors at the published
point; and what the passes would save if every rank-one factor could be made a single block at once
(an upper bound: the orbit point that does it need not exist, nor be accurate).
"""
import sys, numpy as np
sys.path.insert(0, '/Users/greg/projects/logic/matmul/levels')
from levels import parse_sms
D = '/Users/greg/projects/logic/matmul/dps48/plinopt/data/'
SCHEMES = [('3x3x6_40_DPS-accurate', (3, 3, 6)), ('3x3x6_40', (3, 3, 6)), ('4x4x4_48_accurate_262', (4, 4, 4)),
           ('4x4x4_48_accurate', (4, 4, 4)), ('2x2x2_7_DPS-accurate', (2, 2, 2)), ('2x2x2_7_DPS-evenpow-12.2034', (2, 2, 2)),
           ('2x2x2_7_Winograd', (2, 2, 2)), ('2x2x2_7_Strassen', (2, 2, 2))]
def rk(M): return int(np.linalg.matrix_rank(M, tol=1e-9))
for name, (g1, g2, g3) in SCHEMES:
    try:
        L, R, P = (parse_sms(D + f'{name}_{s}.sms') for s in 'LRP')
    except Exception as e:
        print(name, 'unreadable:', e); continue
    r = L.shape[0]
    if P.shape[1] != r: P = P.T
    rx = [rk(L[i].reshape(g1, g2)) for i in range(r)]
    ry = [rk(R[i].reshape(g2, g3)) for i in range(r)]
    rz = [rk(P[:, i].reshape(g1, g3)) for i in range(r)]
    prof = lambda v: ' '.join(f'rank{k}:{v.count(k)}' for k in sorted(set(v)))
    sl = int(((L != 0).sum(1) == 1).sum()); sr = int(((R != 0).sum(1) == 1).sum()); sp = int(((P != 0).sum(0) == 1).sum())
    # distinct directions among the rank-one left factors: columns (u) and rows (v) up to scale
    def dirs(Ms):
        us, vs = [], []
        for M in Ms:
            U, S, Vt = np.linalg.svd(M)
            u, v = U[:, 0], Vt[0]
            for lst, x in ((us, u), (vs, v)):
                x = x / np.linalg.norm(x); x = x * np.sign(x[np.argmax(np.abs(x))])
                if not any(np.allclose(x, y, atol=1e-7) for y in lst): lst.append(x)
        return len(us), len(vs)
    X1 = [L[i].reshape(g1, g2) for i in range(r) if rx[i] == 1]
    Y1 = [R[i].reshape(g2, g3) for i in range(r) if ry[i] == 1]
    both = sum(1 for i in range(r) if rx[i] == 1 and ry[i] == 1)
    T = 3 + r * (1 / (g1 * g2) + 1 / (g2 * g3) + 1 / (g1 * g3))
    cap_l, cap_r = min(len(X1), g1 * g2), min(len(Y1), g2 * g3)
    Tbest = T - cap_l / (g1 * g2) - cap_r / (g2 * g3)
    print(f'{name}: r={r}')
    print(f'   left factors  {prof(rx)};  right {prof(ry)};  output {prof(rz)};  both left and right rank one: {both}')
    if X1: print(f'   rank-one left factors use {dirs(X1)[0]} column and {dirs(X1)[1]} row directions (grid {g1} x {g2});'
                 f' right: {dirs(Y1)[0] if Y1 else 0} and {dirs(Y1)[1] if Y1 else 0} (grid {g2} x {g3})')
    print(f'   single blocks at this point: L {sl}, R {sr}, P {sp};  traffic {T:.2f} n^2; with every possible single block'
          f' (L {cap_l}, R {cap_r}) at best {Tbest:.2f} ({100 * (1 - Tbest / T):.0f}% less)')
