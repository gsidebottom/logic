"""Can a non-orthogonal dyadic isotropy lower the leaf amplification of 4x4x4_48_accurate_262?

amp = max_j sqrt(sum_i p_ji^2 |L_i|_2^2 |R_i|_2^2) / 2 is how much one level of the scheme
amplifies the leaf products' own errors in the realized rounding model (slpopt); it is 2 sqrt2 for
accurate_262 and for every dyadic orthogonal point with the smallest value.  Simulated annealing
over (U, V, W) in GL_4(Z[1/2])^3, moves = left multiplication by an elementary dyadic matrix
(I + c e_i e_j^T, c in {+-1, +-1/2, +-2}), a row swap, or a row scaling by 2^{+-1}, with the
entries' denominators kept at most 2^6; objective amp, ties broken by the mean over outputs.
Every (U, V, W) gives a dyadic scheme (the action's coefficients are dyadic), and amp is invariant
under per-product rescaling, so the value is the scheme's.

  python3 ampwalk.py [restarts] [steps] [seed]
"""
import os, sys, time
import numpy as np
np.seterr(all="ignore")
import orbit

restarts = int(sys.argv[1]) if len(sys.argv) > 1 else 8
steps = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
HERE = os.path.dirname(os.path.abspath(__file__))
L0, R0, P0 = orbit.load(os.path.join(HERE, "..", "plinopt", "data", "4x4x4_48_accurate_262"))

def amp(L, R, P):
    g = (L * L).sum(1) * (R * R).sum(1)            # |L_i|^2 |R_i|^2
    a = np.sqrt((P * P) @ g) / 2                    # per output
    return a.max(), a.mean()

def dyadic_ok(M, maxden=64):
    return np.all(np.abs(M * maxden - np.round(M * maxden)) < 1e-9)

def move(M, rng):
    M = M.copy()
    k = rng.integers(0, 3)
    i, j = rng.integers(0, 4, size=2)
    if k == 0 and i != j:                           # shear
        c = rng.choice([1, -1, 0.5, -0.5, 2, -2])
        M[i] += c * M[j]
    elif k == 1 and i != j:                         # swap
        M[[i, j]] = M[[j, i]]
    else:                                           # scale a row by 2 or 1/2
        M[i] *= rng.choice([2, 0.5])
    return M

def run(k):
    rng = np.random.default_rng(seed * 1000 + k)
    U, V, W = (np.eye(4) for _ in range(3))
    L, R, P = orbit.act(L0, R0, P0, U, V, W)
    cur = amp(L, R, P)
    best = (cur, (U.copy(), V.copy(), W.copy()))
    t0, t1 = 0.05, 0.0005
    for s in range(steps):
        T = t0 * (t1 / t0) ** (s / steps)
        which = rng.integers(0, 3)
        mats = [U, V, W]
        cand = move(mats[which], rng)
        if abs(np.linalg.det(cand)) < 1e-9 or not dyadic_ok(cand) or np.abs(cand).max() > 8:
            continue
        inv = np.linalg.inv(cand)
        if not dyadic_ok(inv):
            continue
        mats[which] = cand
        L, R, P = orbit.act(L0, R0, P0, *mats)
        f = amp(L, R, P)
        d = (f[0] - cur[0]) + 0.1 * (f[1] - cur[1])
        if d <= 0 or rng.random() < np.exp(-d / T):
            U, V, W = mats
            cur = f
            if f[0] < best[0][0] - 1e-12 or (abs(f[0] - best[0][0]) < 1e-12 and f[1] < best[0][1] - 1e-12):
                best = (f, (U.copy(), V.copy(), W.copy()))
        else:
            mats[which] = [U, V, W][which]
    return best

print(f"# ampwalk: accurate_262 amp {amp(L0, R0, P0)[0]:.4f} (mean {amp(L0, R0, P0)[1]:.4f}); {restarts} restarts x {steps} steps")
t = time.time()
results = [run(k) for k in range(restarts)]
for k, ((a, m), (U, V, W)) in enumerate(results):
    print(f"restart {k}: amp {a:.4f} mean {m:.4f}  max |entry| U {np.abs(U).max():.2g} V {np.abs(V).max():.2g} W {np.abs(W).max():.2g}")
(a, m), (U, V, W) = min(results, key=lambda r: (r[0][0], r[0][1]))
print(f"best amp {a:.4f} mean {m:.4f} in {time.time() - t:.0f} s")
np.save("/tmp/claude-501/ampwalk_best.npy", np.stack([U, V, W]))
L, R, P = orbit.act(L0, R0, P0, U, V, W)
print("gamma_inf2 of the best:", orbit.g_inf2(L, R, P), " gamma_inf_inf:", orbit.g_inf_inf(L, R, P), " brent:", orbit.brent_error(L, R, P))
