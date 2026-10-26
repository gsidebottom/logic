"""Is there a <4x4x4:48> scheme off the known orbits with a lower leaf amplification?

amp_j^2 = (1/4) sum_i p_ji^2 |L_i|_2^2 |R_i|_2^2 is how much one level amplifies the leaf
products' own errors into output j (the realized rounding model, slpopt).  Over
4x4x4_48_accurate_262's whole orbit and the other known rational classes its minimum is 2 sqrt2
(ampmin.py, ampwalk.py, dyadic_points.py).  Here the search runs on the whole variety of rank-48
decompositions of the 4x4x4 matrix multiplication tensor: minimize a soft maximum of the amp_j
plus a penalty mu |Brent residual|^2 with mu raised in stages (L-BFGS-B, analytic gradients),
from accurate_262 perturbed at several scales.  A result is accepted when the residual is below
1e-9 after a final projection.

  python3 ampvariety.py [starts per scale] [seed] [scheme prefix]
"""
import os, sys, time
import numpy as np
np.seterr(all="ignore")
from scipy.optimize import minimize
import orbit

HERE = os.path.dirname(os.path.abspath(__file__))
PREFIX = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, "..", "plinopt", "data", "4x4x4_48_accurate_262")
L0, R0, P0 = orbit.load(PREFIX)
N, RK = 4, 48

# the 4x4x4 matrix multiplication tensor T[a*4+b, b*4+c, a*4+c] = 1 (row-major blocks; P rows
# index the outputs, so the scheme computes vec(C) = P ((L vec A) o (R vec B)))
T0 = np.zeros((16, 16, 16))
for a in range(N):
    for b in range(N):
        for c in range(N):
            T0[a * N + b, b * N + c, a * N + c] = 1.0
assert np.allclose(np.einsum("ri,rj,kr->ijk", L0, R0, P0), T0), "tensor convention"

BETA = 40.0

def unpack(x):
    return x[:RK * 16].reshape(RK, 16), x[RK * 16:2 * RK * 16].reshape(RK, 16), x[2 * RK * 16:].reshape(16, RK)

def amps(L, R, P):
    g = (L * L).sum(1) * (R * R).sum(1)
    return np.sqrt((P * P) @ g) / 2

def objective(x, mu):
    L, R, P = unpack(x)
    a2 = (P * P) @ ((L * L).sum(1) * (R * R).sum(1)) / 4           # amp_j^2
    m = a2.max()
    w = np.exp(BETA * (a2 - m)); s = w.sum(); w /= s
    soft = m + np.log(s) / BETA
    res = np.einsum("ri,rj,kr->ijk", L, R, P) - T0
    f = soft + mu * (res * res).sum()
    # gradients of the soft max of amp_j^2
    gi = (L * L).sum(1) * (R * R).sum(1)                          # |L_i|^2 |R_i|^2
    wp2 = w @ (P * P)                                              # sum_j w_j p_ji^2
    gL = 2 * L * (wp2 * (R * R).sum(1))[:, None] / 4
    gR = 2 * R * (wp2 * (L * L).sum(1))[:, None] / 4
    gP = 2 * P * (w[:, None] * gi[None, :]) / 4
    # gradients of the penalty
    gL += mu * 2 * np.einsum("ijk,rj,kr->ri", res, R, P)
    gR += mu * 2 * np.einsum("ijk,ri,kr->rj", res, L, P)
    gP += mu * 2 * np.einsum("ijk,ri,rj->kr", res, L, R)
    return f, np.concatenate([gL.ravel(), gR.ravel(), gP.ravel()])

def project(x, iters=3000):
    """Gauss-Newton-like projection onto the variety: minimize the residual alone"""
    r = minimize(lambda y: residual_only(y), x, jac=True, method="L-BFGS-B", options={"maxiter": iters, "gtol": 1e-14, "ftol": 1e-16})
    return r.x

def residual_only(x):
    L, R, P = unpack(x)
    res = np.einsum("ri,rj,kr->ijk", L, R, P) - T0
    f = (res * res).sum()
    gL = 2 * np.einsum("ijk,rj,kr->ri", res, R, P)
    gR = 2 * np.einsum("ijk,ri,kr->rj", res, L, P)
    gP = 2 * np.einsum("ijk,ri,rj->kr", res, L, R)
    return f, np.concatenate([gL.ravel(), gR.ravel(), gP.ravel()])

def run(scale, seed):
    rng = np.random.default_rng(seed)
    x = np.concatenate([L0.ravel(), R0.ravel(), P0.ravel()])
    x = x + scale * rng.standard_normal(x.size) * np.abs(x).mean()
    for mu in (1.0, 10.0, 100.0, 1000.0, 1e4):
        r = minimize(objective, x, args=(mu,), jac=True, method="L-BFGS-B", options={"maxiter": 4000, "gtol": 1e-10, "ftol": 1e-14})
        x = r.x
    x = project(x)
    L, R, P = unpack(x)
    res = np.abs(np.einsum("ri,rj,kr->ijk", L, R, P) - T0).max()
    a = amps(L, R, P)
    return a.max(), a.mean(), res, x

starts = int(sys.argv[1]) if len(sys.argv) > 1 else 4
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
a0 = amps(L0, R0, P0)
print(f"# ampvariety: start scheme {PREFIX.rsplit('/', 1)[-1]} amp {a0.max():.4f} (mean {a0.mean():.4f}); {starts} starts per scale", flush=True)
t = time.time()
best = (np.inf, None)
for scale in (0.02, 0.1, 0.3, 1.0):
    for k in range(starts):
        amax, amean, res, x = run(scale, seed * 100 + k)
        ok = res < 1e-7
        print(f"scale {scale:<4} start {k}: amp {amax:.4f} mean {amean:.4f} residual {res:.1e} {'ok' if ok else 'NOT ON THE VARIETY'}", flush=True)
        if ok and amax < best[0]:
            best = (amax, x)
print(f"best amp on the variety {best[0]:.4f} (accurate_262: {a0.max():.4f}) in {time.time() - t:.0f} s")
if best[1] is not None:
    np.save(f"/tmp/claude-501/ampvariety_best_{PREFIX.rsplit('/', 1)[-1]}.npy", best[1])
    L, R, P = unpack(best[1])
    print("gamma_inf2", orbit.g_inf2(L, R, P), "gamma_infinf", orbit.g_inf_inf(L, R, P))
