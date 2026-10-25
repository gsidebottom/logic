"""gamma_{inf,2} over the orthogonal sub-orbit of a scheme: U, W in SO(4) (V drops out: the row
norms of L and R are invariant, so gamma_2 stays fixed); only the outputs rotate,
P'_i = vec(U Z_i W^T).  Rotations by the Cayley transform Q = (I - S)(I + S)^-1 of a skew S
(rational S gives a rational orthogonal Q).  Smoothed objective (log-sum-exp of the max,
sqrt(x^2 + eps^2) for |x|) by BFGS with continuation, then Nelder-Mead on the true max.

  python3 search_orth.py SCHEME ROLE STARTS SEED
"""
import sys, time
import numpy as np
np.seterr(all="ignore")   # numpy on Accelerate raises spurious FP flags in matmul
from scipy.optimize import minimize
from multiprocessing import Pool
import orbit

IU = np.triu_indices(4, 1)

def cayley(s):
    S = np.zeros((4, 4))
    S[IU] = s
    S -= S.T
    I = np.eye(4)
    return (I - S) @ np.linalg.inv(I + S)

class Problem:
    def __init__(self, L, R, P):
        self.w = np.linalg.norm(L, axis=1) * np.linalg.norm(R, axis=1)
        self.Z = P.T.reshape(-1, 4, 4)                  # Z_i, row-major outputs

    def v(self, x, eps=0.0):
        U, W = cayley(x[:6]), cayley(x[6:])
        Zp = np.einsum("pa,iab,qb->ipq", U, self.Z, W)  # U Z_i W^T
        a = np.sqrt(Zp * Zp + eps * eps) if eps else np.abs(Zp)
        return np.einsum("i,ipq->pq", self.w, a).ravel()

    def true(self, x):
        return self.v(x).max()

    def smooth(self, x, beta, eps):
        v = self.v(x, eps)
        m = v.max()
        return m + np.log(np.exp(beta * (v - m)).sum()) / beta

def run(args):
    L, R, P, seed = args
    rng = np.random.default_rng(seed)
    pr = Problem(L, R, P)
    x = rng.normal(scale=[0.05, 0.5, 1.5][seed % 3], size=12) if seed else np.zeros(12)
    for beta, eps in [(0.5, 1e-1), (2.0, 3e-2), (8.0, 1e-2), (32.0, 3e-3), (128.0, 1e-3)]:
        x = minimize(pr.smooth, x, args=(beta, eps), method="BFGS", options={"gtol": 1e-8, "maxiter": 2000}).x
    x = minimize(pr.true, x, method="Nelder-Mead", options={"xatol": 1e-10, "fatol": 1e-12, "maxiter": 20000, "maxfev": 40000}).x
    return pr.true(x), seed, x

if __name__ == "__main__":
    name, role, starts, seed0 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    L, R, P = orbit.roles(*orbit.load(orbit.SCHEMES[name]))[role]
    g0 = orbit.g_inf2(L, R, P)
    t = time.time()
    with Pool(12) as pool:
        res = sorted(pool.map(run, [(L, R, P, seed0 + s) for s in range(starts)]), key=lambda r: r[0])
    print(f"# {name} role {role}: start g(inf,2) {g0:.4f}, gamma2 {orbit.g2(L, R, P):.4f}; {starts} starts in {time.time() - t:.0f} s")
    print("# best ten:", " ".join(f"{g:.4f}" for g, _, _ in res[:10]))
    g, s, x = res[0]
    U, W = cayley(x[:6]), cayley(x[6:])
    L2, R2, P2 = orbit.act(L, R, P, U, np.eye(4), W)
    print(f"# best: seed {s}  g(inf,2) {orbit.g_inf2(L2, R2, P2):.6f}  gamma2 {orbit.g2(L2, R2, P2):.6f}  "
          f"g(inf,inf) {orbit.g_inf_inf(L2, R2, P2):.3f}  brent err {orbit.brent_error(L2, R2, P2):.1e}")
    np.save(f"orth_{name}_r{role}_best.npy", x)
    print("# x =", np.array2string(x, precision=6, max_line_width=200))
