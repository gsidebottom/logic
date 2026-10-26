# Continuous infimum of the leaf amplification over the orbit (no dyadic constraint): is 2 sqrt2 a floor?
import os, sys, time
import numpy as np
np.seterr(all="ignore")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import orbit
from scipy.optimize import minimize
PREFIX = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "plinopt", "data", "4x4x4_48_accurate_262")
L0, R0, P0 = orbit.load(PREFIX)
print("# scheme", PREFIX)
def amp_vec(x):
    U, V, W = x[:16].reshape(4, 4), x[16:32].reshape(4, 4), x[32:].reshape(4, 4)
    L, R, P = orbit.act(L0, R0, P0, U, V, W)
    g = (L * L).sum(1) * (R * R).sum(1)
    return np.sqrt((P * P) @ g) / 2
def f(x, beta=30.0):   # soft max over outputs
    a = amp_vec(x)
    m = a.max()
    return m + np.log(np.exp(beta * (a - m)).sum()) / beta
rng = np.random.default_rng(1)
best = (np.inf, None)
t = time.time()
for k in range(12):
    x0 = np.concatenate([np.eye(4).ravel()] * 3) + (0.0 if k == 0 else 0.3) * rng.standard_normal(48)
    r = minimize(f, x0, method="BFGS", options={"maxiter": 2000, "gtol": 1e-8})
    a = amp_vec(r.x)
    print(f"start {k}: amp max {a.max():.4f} mean {a.mean():.4f} (soft {r.fun:.4f}, {r.nit} it)", flush=True)
    if a.max() < best[0]:
        best = (a.max(), r.x)
print(f"best continuous amp {best[0]:.4f} in {time.time()-t:.0f} s; at the start: {amp_vec(np.concatenate([np.eye(4).ravel()]*3)).max():.4f}")
U, V, W = best[1][:16].reshape(4,4), best[1][16:32].reshape(4,4), best[1][32:].reshape(4,4)
print("singular values U", np.round(np.linalg.svd(U, compute_uv=False), 3), "V", np.round(np.linalg.svd(V, compute_uv=False), 3), "W", np.round(np.linalg.svd(W, compute_uv=False), 3))
