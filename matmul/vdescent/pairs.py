#!/usr/bin/env python3
"""pairs.py: descent on the variety of exact decompositions toward a reduction (2026-11-14).

Two products can be merged into one when they are parallel in two of their three factors.  For
products s, t and a slot X let p^X_st = 1 - cos^2 of the angle between X_s and X_t, and

    D_st = p^U p^V + p^U p^W + p^V p^W        (zero exactly when two of the three vanish),
    Phi(x) = sum_{s<t} omega_st log(D_st + delta).

Phi falls without bound (as delta -> 0) where a pair becomes mergeable, so minimizing it over the
variety V_r of exact rank-r decompositions is a continuous search for a reduction: the flip
graph's random walk with a compass.  A step solves (J^T J + lam) d = -(J^T F + mu grad Phi): the
Gauss-Newton part holds the point on V_r, and in the kernel of the Jacobian, the tangent space,
the step is descent of Phi; lam adapts to the decrease of 1/2 |F|^2 + mu Phi.  Pairs with D below
a threshold are merged, the scheme is polished back to |F| = 0 at the smaller rank (or the merge
is refused), and the descent goes on.  Random pair weights omega break the symmetry of the start.

   pairs.py SCHEME [--runs R] [--seed S] [--steps N] [--mu MU] [--split M] [--out DIR] [--verbose]
"""
import sys, os, time, numpy as np
from scipy.linalg import cho_factor, cho_solve, LinAlgError
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from vd import tensor, residual, load, trivial, normal_matrix, trivial_tangents
from descend import grad_F, unpack, balance, lm, split

def potential(U, V, W, om, delta, want_grad=True):
    P, G, n = [], [], []
    for X in (U, V, W):
        g = X @ X.T; d = np.maximum(np.diag(g), 1e-300)
        G.append(g); n.append(d); P.append(1 - g * g / np.outer(d, d))
    D = P[0] * P[1] + P[0] * P[2] + P[1] * P[2]
    iu = np.triu_indices(U.shape[0], 1)
    phi = float((om[iu] * np.log(D[iu] + delta)).sum())
    if not want_grad: return phi, D
    grads = []
    for q, X in enumerate((U, V, W)):
        o1, o2 = [s for s in range(3) if s != q]
        A = om * (P[o1] + P[o2]) / (D + delta); np.fill_diagonal(A, 0)
        c = G[q] * G[q] / np.outer(n[q], n[q])
        M = -2 * A * G[q] / np.outer(n[q], n[q])
        diag = (2 * A * c).sum(1) / n[q]
        grads.append(M @ X + diag[:, None] * X)
    return phi, D, np.concatenate([x.ravel() for x in grads])

def merge_pairs(U, V, W, D, T, thresh):
    """merge the most mergeable pair if D < thresh and the merged scheme polishes to |F| = 0"""
    r = U.shape[0]
    Dm = D + np.tril(np.ones((r, r))) * 10
    s, t = np.unravel_index(np.argmin(Dm), Dm.shape)
    if Dm[s, t] > thresh: return None
    X = [U, V, W]
    par = [abs(X[q][s] @ X[q][t]) / (np.linalg.norm(X[q][s]) * np.linalg.norm(X[q][t]) + 1e-300) for q in range(3)]
    free = int(np.argmin(par))                      # the slot that is not parallel carries the sum
    scale = 1.0
    for q in range(3):
        if q != free: scale *= (X[q][s] @ X[q][t]) / (X[q][s] @ X[q][s])
    Y = [x.copy() for x in X]
    Y[free][s] = X[free][s] + scale * X[free][t]
    keep = np.arange(r) != t
    U2, V2, W2 = (y[keep] for y in Y)
    U2, V2, W2, f, _ = lm(*balance(U2, V2, W2), T, 0.0, np.ones(r - 1), 200, lam=1e-6, tol=1e-13)
    return (U2, V2, W2) if f < 1e-10 else None

def moduli_basis(g, U, V, W):
    """an orthonormal basis of the tangent directions of the variety that are not rescalings of
    products or moves along the group orbit: the kernel of the Jacobian with the trivial tangents
    projected out.  Moving along the orbit changes no scheme but changes every angle (a GL element
    that squashes a direction makes all factors look parallel), so the descent must not use it."""
    ev, evec = np.linalg.eigh(normal_matrix(U, V, W))
    null = evec[:, ev < 1e-9 * ev[-1]]
    Q, sq, _ = np.linalg.svd(trivial_tangents(g, U, V, W).T, full_matrices=False)
    Q = Q[:, sq > 1e-8 * sq[0]]
    Zm = null - Q @ (Q.T @ null)
    u, sv, _ = np.linalg.svd(Zm, full_matrices=False)
    return u[:, sv > 1e-6]

def run(g, U, V, W, rng, steps=200, mu=0.0, verbose=False, target=0, kick_size=0.3, bound=30.0):
    """predictor-corrector descent of Phi along the moduli; returns (rank, |F|, U, V, W, log)"""
    T = tensor(*g)
    U, V, W = balance(U, V, W)
    r = U.shape[0]; I, J, K = U.shape[1], V.shape[1], W.shape[1]
    om = np.exp(rng.standard_normal((r, r))); om = (om + om.T) / 2
    delta = 1e-2; eta = kick_size; stall = 0; log = []
    nmax = bound * ((U ** 2).sum(1) + (V ** 2).sum(1) + (W ** 2).sum(1)).max()    # no product may grow past this:
    # a pair that becomes parallel while its norms diverge is a degeneration, not a reduction
    for it in range(steps):
        M = moduli_basis(g, U, V, W)
        if M.shape[1] == 0:
            log.append(f"step {it}: rigid at {r} products (no moduli)"); break
        phi, D, gp = potential(U, V, W, om[:r, :r], delta)
        x = np.concatenate([U.ravel(), V.ravel(), W.ravel()])
        d = -M @ (M.T @ gp)
        if np.linalg.norm(d) < 1e-9 * (1 + np.linalg.norm(gp)) or stall >= 2 or eta < 1e-3:   # a critical point or a
            # local minimum of Phi on the moduli: a random move (the walk of a flip graph, continuous)
            eta = kick_size
            d = M @ rng.standard_normal(M.shape[1]); kicked = True; stall = 0
        else:
            kicked = False
        d *= np.linalg.norm(x) / np.sqrt(r) / np.linalg.norm(d)
        moved = False
        for _ in range(8):
            U2, V2, W2, f, _ = lm(*unpack(x + eta * d, r, I, J, K), T, 0.0, np.ones(r), 60, lam=1e-6, tol=1e-13)
            if f < 1e-10:
                U2, V2, W2 = balance(U2, V2, W2)
                phi2, D2 = potential(U2, V2, W2, om[:r, :r], delta, False)
                if ((U2 ** 2).sum(1) + (V2 ** 2).sum(1) + (W2 ** 2).sum(1)).max() > nmax:
                    eta *= 0.5; continue
                if kicked or phi2 < phi:
                    U, V, W, D = U2, V2, W2, D2; moved = True; eta = min(eta * 1.5, 1.0); break
            eta *= 0.5
        if not moved: stall += 1; eta = kick_size
        while True:
            m = merge_pairs(U, V, W, D, T, 1e-4)
            if m is None: break
            U, V, W = balance(*m); r -= 1
            om = np.exp(rng.standard_normal((r, r))); om = (om + om.T) / 2
            _, D = potential(U, V, W, om, delta, False)
            log.append(f"step {it}: merged a pair, {r} products")
            if verbose: print("      " + log[-1], flush=True)
        delta = max(delta * 0.9, 1e-7)
        if verbose and it % 10 == 0:
            n2 = (U ** 2).sum(1) + (V ** 2).sum(1) + (W ** 2).sum(1)
            print(f"      step {it}: {r} products, moduli {M.shape[1]}, min D {np.sort(D[np.triu_indices(r, 1)])[:3].round(5)}, "
                  f"norms {n2.min():.2f}..{n2.max():.2f}, eta {eta:.2g}{' (kick)' if kicked else ''}", flush=True)
        if target and r <= target: break
    U, V, W, f, _ = lm(U, V, W, T, 0.0, np.ones(r), 300, lam=1e-6, tol=1e-13)
    return r, f, U, V, W

if __name__ == '__main__':
    a = sys.argv[1:]
    opt = lambda k, dflt: type(dflt)(a[a.index(k) + 1]) if k in a else dflt
    src = a[0]
    runs, seed, steps, mu, m, out, target = opt('--runs', 8), opt('--seed', 1), opt('--steps', 200), opt('--mu', 1e-3), opt('--split', 0), opt('--out', ''), opt('--target', 0)
    ksize = opt('--kick', 0.3); bound = opt('--bound', 30.0)
    if '--gradcheck' in a:
        rng = np.random.default_rng(0); U, V, W = (rng.standard_normal((5, k)) for k in (4, 6, 3))
        om = np.exp(rng.standard_normal((5, 5))); om = (om + om.T) / 2
        phi, D, gr = potential(U, V, W, om, 1e-2)
        x = np.concatenate([U.ravel(), V.ravel(), W.ravel()]); num = np.zeros_like(x)
        for i in range(len(x)):
            e = np.zeros_like(x); e[i] = 1e-6
            num[i] = (potential(*unpack(x + e, 5, 4, 6, 3), om, 1e-2, False)[0] - potential(*unpack(x - e, 5, 4, 6, 3), om, 1e-2, False)[0]) / 2e-6
        print("gradient check: max abs difference", np.abs(num - gr).max(), "of", np.abs(gr).max()); sys.exit()
    if src.startswith('trivial:'):
        g = tuple(int(x) for x in src[8:].split('x')); U0, V0, W0 = trivial(*g)
    else:
        g, U0, V0, W0 = load(src)
    r0 = U0.shape[0]
    print(f"# {src.split('/')[-1]}: <{g[0]}x{g[1]}x{g[2]}:{r0}>, {m} splits, {runs} runs from seed {seed}, {steps} steps, mu {mu}", flush=True)
    hist = {}; t0 = time.time()
    for k in range(runs):
        rng = np.random.default_rng(seed * 1000 + k)
        U, V, W = split(U0, V0, W0, m, rng) if m else (U0, V0, W0)
        rk, f, U, V, W = run(g, U, V, W, rng, steps=steps, mu=mu, verbose='--verbose' in a, target=target, kick_size=ksize, bound=bound)
        ok = f < 1e-10
        hist[(rk, ok)] = hist.get((rk, ok), 0) + 1
        print(f"run {k}: {r0 + m} -> {rk} products, |F| {f:.1e} {'EXACT' if ok else 'not a scheme'}  ({time.time() - t0:.0f} s)" +
              ("   <== BELOW THE START" if ok and rk < r0 else ""), flush=True)
        if ok and out and rk < r0:
            os.makedirs(out, exist_ok=True)
            np.savez(f"{out}/{g[0]}x{g[1]}x{g[2]}_r{rk}_seed{seed}_run{k}.npz", U=U, V=V, W=W, g=np.array(g), f=f)
    print("# summary: " + ", ".join(f"{k[0]} products {'exact' if k[1] else 'inexact'}: {v}" for k, v in sorted(hist.items())), flush=True)
