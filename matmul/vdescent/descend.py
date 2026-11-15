#!/usr/bin/env python3
"""descend.py: rank descent on the variety of exact decompositions (2026-11-14).

A flip graph moves between schemes by discrete steps over a small ring.  Here the schemes with r
products are the zeros of F(x) = sum_t U_t (x) V_t (x) W_t - T, a real variety V_r, and the
search is continuous: from a known scheme (optionally with some products split in two, the
continuous "plus" move), minimize a sparsity functional of the products over V_r,

    cost(x) = 1/2 |F(x)|^2 + mu/2 sum_t w_t n_t^2,     n_t^2 = |U_t|^2 + |V_t|^2 + |W_t|^2,

by Levenberg-Marquardt steps: the Gauss-Newton part holds x on the variety, and in the kernel of
the Jacobian (the tangent space: rescalings, the group orbit, and the moduli vd.py counts) the
step is plain descent of the penalty.  With the weights w_t = 1 / (n_t^2 + delta) renewed as the
products change (the log-sum surrogate of the number of nonzero products) a product that can
shrink is pushed to zero; when its norm is negligible it is removed, and at the end a polish with
mu = 0 must bring |F| to zero at the smaller rank, or the run has found nothing.  Two products
sharing a factor span a GL_2 family of decompositions of their sum, of which a flip is a discrete
point: the descent's moves contain the flip graph's, with real coefficients.

   descend.py SCHEME [--split M] [--seed S] [--iters N] [--mu MU] [--runs R] [--target RANK] [--out DIR]
SCHEME: a catalog .json, a PLinOpt base name, or trivial:g1xg2xg3.
"""
import sys, time, json, os, numpy as np
from scipy.linalg import cho_factor, cho_solve, LinAlgError
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from vd import tensor, residual, load, trivial, normal_matrix

def grad_F(U, V, W, R):
    return np.concatenate([np.einsum('abc,rb,rc->ra', R, V, W).ravel(), np.einsum('abc,ra,rc->rb', R, U, W).ravel(),
                           np.einsum('abc,ra,rb->rc', R, U, V).ravel()])

def unpack(x, r, I, J, K):
    return x[:r * I].reshape(r, I), x[r * I:r * (I + J)].reshape(r, J), x[r * (I + J):].reshape(r, K)

def balance(U, V, W):
    """rescale each product so that its three factors have equal norms (a point of the same scheme)"""
    nu, nv, nw = (np.linalg.norm(X, axis=1) for X in (U, V, W))
    ok = (nu > 0) & (nv > 0) & (nw > 0)
    g = np.ones_like(nu); g[ok] = (nu[ok] * nv[ok] * nw[ok]) ** (1 / 3)
    su, sv, sw = np.ones_like(nu), np.ones_like(nu), np.ones_like(nu)
    su[ok], sv[ok], sw[ok] = g[ok] / nu[ok], g[ok] / nv[ok], g[ok] / nw[ok]
    return U * su[:, None], V * sv[:, None], W * sw[:, None]

def lm(U, V, W, T, mu, wts, iters, lam=1e-3, tol=0.0, verbose=None):
    """Levenberg-Marquardt on cost; returns U, V, W, |F|_max, iterations used"""
    r, I = U.shape; J = V.shape[1]; K = W.shape[1]
    x = np.concatenate([U.ravel(), V.ravel(), W.ravel()])
    d = np.concatenate([np.repeat(wts, I), np.repeat(wts, J), np.repeat(wts, K)])
    def cost_of(x):
        U, V, W = unpack(x, r, I, J, K)
        R = residual(U, V, W, T)
        return 0.5 * (R ** 2).sum() + 0.5 * mu * (d * x * x).sum(), R
    c, R = cost_of(x)
    it = 0
    for it in range(iters):
        U, V, W = unpack(x, r, I, J, K)
        N = normal_matrix(U, V, W)
        g = grad_F(U, V, W, R) + mu * d * x
        if np.abs(R).max() < tol and mu == 0: break
        for _ in range(30):
            try:
                cf = cho_factor(N + np.diag(mu * d + lam), check_finite=False)
                step = -cho_solve(cf, g, check_finite=False)
            except LinAlgError:
                lam *= 10; continue
            c2, R2 = cost_of(x + step)
            if c2 < c:
                x = x + step; c, R = c2, R2; lam = max(lam / 3, 1e-14); break
            lam *= 4
        else:
            break
        if verbose and it % verbose == 0:
            print(f"      it {it}: cost {c:.3e} |F| {np.abs(R).max():.2e} lam {lam:.1e}", flush=True)
    U, V, W = unpack(x, r, I, J, K)
    return U.copy(), V.copy(), W.copy(), float(np.abs(R).max()), it + 1

def split(U, V, W, m, rng):
    """m continuous plus moves: product t becomes (u, v, w') + (u, v, w - w') in a random slot"""
    U, V, W = U.copy(), V.copy(), W.copy()
    for _ in range(m):
        t = rng.integers(U.shape[0]); s = rng.integers(3)
        X = [U, V, W]
        part = X[s][t] * rng.uniform(0.3, 0.7) + rng.standard_normal(X[s].shape[1]) * 0.5 * np.linalg.norm(X[s][t]) / np.sqrt(X[s].shape[1])
        new = [X[0][t].copy(), X[1][t].copy(), X[2][t].copy()]
        new[s] = part
        X[s][t] = X[s][t] - part
        U, V, W = (np.vstack([X[q], new[q][None]]) for q in range(3))
    return U, V, W

def descend(g, U, V, W, rng, iters=400, mu0=1e-2, rounds=40, kill=1e-3, noise=0.3, verbose=False):
    """one run: returns (rank reached, |F|_max after the polish, U, V, W)"""
    T = tensor(*g)
    U, V, W = balance(U, V, W)
    r = U.shape[0]
    bias = np.exp(noise * rng.standard_normal(r))          # which products the run leans on
    mu = mu0
    for rd in range(rounds):
        n2 = (U ** 2).sum(1) + (V ** 2).sum(1) + (W ** 2).sum(1)
        delta = 1e-2 * np.median(n2) * 0.7 ** rd
        wts = bias / (n2 + delta); wts *= len(wts) / wts.sum()
        U, V, W, f, _ = lm(U, V, W, T, mu, wts, iters // rounds + 1)
        U, V, W = balance(U, V, W)
        n2 = (U ** 2).sum(1) + (V ** 2).sum(1) + (W ** 2).sum(1)
        keep = n2 > kill * np.median(n2)
        if not keep.all():
            U, V, W, bias = U[keep], V[keep], W[keep], bias[keep]
        if verbose:
            print(f"   round {rd}: {U.shape[0]} products, |F| {f:.2e}, smallest n2/median {np.sort(n2 / np.median(n2))[:3].round(4)}", flush=True)
    U, V, W, f, its = lm(U, V, W, T, 0.0, np.ones(U.shape[0]), 300, lam=1e-6, tol=1e-13)
    return U.shape[0], f, U, V, W

if __name__ == '__main__':
    a = sys.argv[1:]
    opt = lambda k, dflt: type(dflt)(a[a.index(k) + 1]) if k in a else dflt
    src = a[0]
    m, seed, iters, mu, runs = opt('--split', 0), opt('--seed', 1), opt('--iters', 400), opt('--mu', 1e-2), opt('--runs', 8)
    target, out, noise, rounds = opt('--target', 0), opt('--out', ''), opt('--noise', 0.3), opt('--rounds', 40)
    if src.startswith('trivial:'):
        g = tuple(int(x) for x in src[8:].split('x')); U0, V0, W0 = trivial(*g)
    else:
        g, U0, V0, W0 = load(src)
    r0 = U0.shape[0]
    print(f"# {src.split('/')[-1]}: <{g[0]}x{g[1]}x{g[2]}:{r0}>, {m} splits, {runs} runs from seed {seed}, {iters} LM steps in {rounds} rounds, mu {mu}", flush=True)
    hist = {}; t0 = time.time()
    for run in range(runs):
        rng = np.random.default_rng(seed * 1000 + run)
        U, V, W = split(U0, V0, W0, m, rng) if m else (U0, V0, W0)
        rk, f, U, V, W = descend(g, U, V, W, rng, iters=iters, mu0=mu, rounds=rounds, noise=noise, verbose='--verbose' in a)
        ok = f < 1e-10
        hist[(rk, ok)] = hist.get((rk, ok), 0) + 1
        tag = 'EXACT' if ok else 'not a scheme'
        print(f"run {run}: {r0 + m} -> {rk} products, |F| {f:.1e} {tag}  ({time.time() - t0:.0f} s)" + ("   <== BELOW THE START" if ok and rk < r0 else "") +
              ("   <== TARGET" if ok and target and rk <= target else ""), flush=True)
        if ok and out and (rk < r0 or (target and rk <= target)):
            os.makedirs(out, exist_ok=True)
            np.savez(f"{out}/{g[0]}x{g[1]}x{g[2]}_r{rk}_seed{seed}_run{run}.npz", U=U, V=V, W=W, g=np.array(g), f=f)
    print("# summary: " + ", ".join(f"{k[0]} products {'exact' if k[1] else 'inexact'}: {v}" for k, v in sorted(hist.items())), flush=True)
