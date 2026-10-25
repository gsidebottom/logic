"""gamma_{inf,2} over the whole De Groot orbit of a scheme: (U, V, W) in GL(4)^3 act as
  Mat(L'_i) = U^-T Mat(L_i) V^T,  Mat(R'_i) = V^-T Mat(R_i) W^T,  Z'_i = U Z_i W^-1
(row-major matrices of the rows of L, R and of the columns of P), so
  v_pq = sum_i ||U^-T A_i V^T||_F ||V^-T B_i W^T||_F |(U Z_i W^-1)_pq|,  gamma = max v.
Smoothed objective (log-sum-exp, sqrt(x^2 + eps^2)) by BFGS with continuation, then Nelder-Mead
on the true max.  Starts: identity, the best orthogonal point (if saved), random near-identity
and random orthogonal-times-near-identity.

  python3 search_gl.py SCHEME ROLE STARTS SEED
"""
import os, sys, time
import numpy as np
np.seterr(all="ignore")
from scipy.optimize import minimize
from multiprocessing import Pool
import orbit
from search_orth import cayley

class Problem:
    def __init__(self, L, R, P):
        r = L.shape[0]
        self.A = L.reshape(r, 4, 4)
        self.B = R.reshape(r, 4, 4)
        self.Z = P.T.reshape(r, 4, 4)

    def v(self, x, eps=0.0):
        U, V, W = x[:16].reshape(4, 4), x[16:32].reshape(4, 4), x[32:].reshape(4, 4)
        try:
            iUT, iVT, iW = np.linalg.inv(U).T, np.linalg.inv(V).T, np.linalg.inv(W)
        except np.linalg.LinAlgError:
            return np.full(16, 1e9)
        nA = np.linalg.norm(np.einsum("pa,iab,qb->ipq", iUT, self.A, V), axis=(1, 2))
        nB = np.linalg.norm(np.einsum("pa,iab,qb->ipq", iVT, self.B, W), axis=(1, 2))
        Zp = np.einsum("pa,iab,bq->ipq", U, self.Z, iW)
        a = np.sqrt(Zp * Zp + eps * eps) if eps else np.abs(Zp)
        return np.einsum("i,ipq->pq", nA * nB, a).ravel()

    def true(self, x):
        v = self.v(x)
        return v.max() if np.all(np.isfinite(v)) else 1e9

    def smooth(self, x, beta, eps):
        v = self.v(x, eps)
        if not np.all(np.isfinite(v)):
            return 1e9
        m = v.max()
        return m + np.log(np.exp(beta * (v - m)).sum()) / beta

def normalize(x):
    """each of U, V, W scaled to determinant +-1 (gamma is invariant under scaling them)"""
    y = x.copy()
    for k in range(3):
        M = y[16 * k:16 * k + 16].reshape(4, 4)
        y[16 * k:16 * k + 16] = (M / abs(np.linalg.det(M)) ** 0.25).ravel()
    return y

def run(args):
    L, R, P, seed, x0 = args
    rng = np.random.default_rng(seed)
    pr = Problem(L, R, P)
    kind = seed % 4
    if seed == 0:
        x = np.concatenate([np.eye(4).ravel()] * 3)
    elif kind == 0 and x0 is not None:
        x = x0 + rng.normal(scale=0.02, size=48)
    elif kind in (0, 1):
        x = np.concatenate([(np.eye(4) + rng.normal(scale=0.15, size=(4, 4))).ravel() for _ in range(3)])
    else:
        x = np.concatenate([(cayley(rng.normal(scale=1.0, size=6)) @ (np.eye(4) + rng.normal(scale=[0.3, 0.6, 1.0][seed % 3], size=(4, 4)))).ravel()
                            for _ in range(3)])
    for beta, eps in [(0.5, 1e-1), (2.0, 3e-2), (8.0, 1e-2), (32.0, 3e-3), (128.0, 1e-3)]:
        x = normalize(minimize(pr.smooth, x, args=(beta, eps), method="BFGS", options={"gtol": 1e-8, "maxiter": 3000}).x)
    x = polish(pr, x)
    return pr.true(x), seed, normalize(x)

def polish(pr, x, eps=1e-7):
    """minimax by SLSQP on the epigraph: min t subject to v_j(x) <= t for every output j"""
    y0 = np.concatenate([x, [pr.true(x)]])
    cons = {"type": "ineq", "fun": lambda y: y[-1] - pr.v(y[:-1], eps)}
    r = minimize(lambda y: y[-1], y0, method="SLSQP", constraints=[cons], options={"maxiter": 500, "ftol": 1e-12})
    y = r.x[:-1] if np.all(np.isfinite(r.x)) and pr.true(r.x[:-1]) < pr.true(x) else x
    return normalize(y)

if __name__ == "__main__":
    name, role, starts, seed0 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    L, R, P = orbit.roles(*orbit.load(orbit.SCHEMES[name]))[role]
    x0 = None
    f = f"orth_{name}_r{role}_best.npy"
    if os.path.exists(f):
        xo = np.load(f)
        x0 = np.concatenate([cayley(xo[:6]).ravel(), np.eye(4).ravel(), cayley(xo[6:]).ravel()])
    t = time.time()
    with Pool(12) as pool:
        res = sorted(pool.map(run, [(L, R, P, seed0 + s, x0) for s in range(starts)]), key=lambda r: r[0])
    print(f"# {name} role {role}: start g(inf,2) {orbit.g_inf2(L, R, P):.4f}; {starts} starts in {time.time() - t:.0f} s")
    print("# best ten:", " ".join(f"{g:.4f}" for g, _, _ in res[:10]))
    g, s, x = res[0]
    U, V, W = x[:16].reshape(4, 4), x[16:32].reshape(4, 4), x[32:].reshape(4, 4)
    L2, R2, P2 = orbit.act(L, R, P, U, V, W)
    print(f"# best: seed {s}  g(inf,2) {orbit.g_inf2(L2, R2, P2):.6f}  gamma2 {orbit.g2(L2, R2, P2):.4f}  "
          f"g(inf,inf) {orbit.g_inf_inf(L2, R2, P2):.3f}  brent err {orbit.brent_error(L2, R2, P2):.1e}")
    np.save(f"gl_{name}_r{role}_best.npy", x)
    for nm, M in zip("UVW", (U, V, W)):
        print(f"# {nm} =", np.array2string(M, precision=5, suppress_small=True, max_line_width=200).replace("\n", " "))
