#!/usr/bin/env python3
"""A bounded numerical look for a decomposition of <g1 x g2 x g3> of a given rank over the reals
(2026-11-14): regularized alternating least squares from random starts, the regularization
lowered as the residual falls.  A start "converges" when the residual of the matrix
multiplication tensor falls below 1e-9.  Validated on ranks that are known to exist before a
rank that is not: a method that cannot find the known rank says nothing about the unknown one.

   als_rank.py g1 g2 g3 rank [starts] [sweeps] [seed]
"""
import sys, time, numpy as np
g1, g2, g3, r = (int(x) for x in sys.argv[1:5])
starts = int(sys.argv[5]) if len(sys.argv) > 5 else 8
sweeps = int(sys.argv[6]) if len(sys.argv) > 6 else 20000
seed = int(sys.argv[7]) if len(sys.argv) > 7 else 0
I, J, K = g1 * g2, g2 * g3, g3 * g1
T = np.zeros((I, J, K))
for i in range(g1):
    for j in range(g2):
        for k in range(g3):
            T[i * g2 + j, j * g3 + k, k * g1 + i] = 1
T1 = T.reshape(I, J * K); T2 = T.transpose(1, 0, 2).reshape(J, I * K); T3 = T.transpose(2, 0, 1).reshape(K, I * J)
def kr(A, B):      # Khatri-Rao, rows indexed (a, b)
    return (A[:, None, :] * B[None, :, :]).reshape(-1, A.shape[1])
rng = np.random.default_rng(seed)
best = (1e9, None); conv = 0; t0 = time.time()
for s in range(starts):
    U, V, W = (rng.standard_normal((n, r)) for n in (I, J, K))
    lam = 1e-1; res = 1e9
    for it in range(sweeps):
        G = (V.T @ V) * (W.T @ W) + lam * np.eye(r); U = np.linalg.solve(G, (T1 @ kr(V, W)).T + lam * U.T).T
        G = (U.T @ U) * (W.T @ W) + lam * np.eye(r); V = np.linalg.solve(G, (T2 @ kr(U, W)).T + lam * V.T).T
        G = (U.T @ U) * (V.T @ V) + lam * np.eye(r); W = np.linalg.solve(G, (T3 @ kr(U, V)).T + lam * W.T).T
        lam = max(1e-12, 0.1 * np.exp(-25.0 * it / sweeps))     # the regularization decays over the run
        if it % 50 == 49:
            res = np.linalg.norm(T1 - U @ kr(V, W).T)
            lam = min(lam, max(1e-13, 0.3 * res * res))
            if res < 1e-9: break
    mx = max(np.abs(U).max(), np.abs(V).max(), np.abs(W).max())
    conv += res < 1e-9
    if res < best[0]: best = (res, mx)
    if res < 1e-9 or s % 10 == 9:
        print(f"<{g1}x{g2}x{g3}:{r}> start {s}: residual {res:.3e} after {it + 1} sweeps, largest coefficient {mx:.1f}, "
              f"{conv} converged so far, best residual {best[0]:.3e}, {time.time() - t0:.0f} s", flush=True)
print(f"<{g1}x{g2}x{g3}:{r}>: {conv} of {starts} starts converged; best residual {best[0]:.3e}")
