#!/usr/bin/env python3
"""Orbit minima of amp, gamma_{inf,2} and gamma_2 for a <g1 x g2 x g3 : r> scheme under
GL_g1 x GL_g2 x GL_g3 (L -> L kron(U^-1, V^T), R -> R kron(V^-1, W^T), P -> kron(U, W^-T) P),
L-BFGS from random starts with smoothed maxima, as ../gamma5/orbit5.py for square shapes.
  python3 -I orbit_rect.py OUT.csv PREFIX g1 g2 g3 [--starts 8] [--jobs 12] [--maxiter 400]
PREFIX_{L,R,P}.sms in PLinOpt's format, our convention."""
import csv, math, os, sys
if sys.flags.isolated:
    sys.path.append("/Users/greg/Library/Python/3.9/lib/python/site-packages")
    sys.path.append(os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from multiprocessing import Pool
from scipy.optimize import minimize
import levels

def transformed(L, R, P, U, V, W):
    return L @ np.kron(np.linalg.inv(U), V.T), R @ np.kron(np.linalg.inv(V), W.T), np.kron(U, np.linalg.inv(W).T) @ P

def quantities(L, R, P):
    l2, r2 = np.linalg.norm(L, axis=1), np.linalg.norm(R, axis=1)
    s2 = np.abs(P) @ (l2 * r2)
    amp = 0.5 * np.sqrt((P ** 2) @ (l2 ** 2 * r2 ** 2))
    return dict(amp=float(amp.max()), g_inf2=float(s2.max()), g_2=float(np.sum(l2 * r2 * np.linalg.norm(P, axis=0))),
                g_infinf=float((np.abs(P) @ (np.abs(L).sum(1) * np.abs(R).sum(1))).max()))

def unpack(x, g):
    mats, pos = [], 0
    for n in g:
        mats.append(np.eye(n) + x[pos:pos + n * n].reshape(n, n)); pos += n * n
    return mats

def smooth_obj(kind, beta, g):
    def f(x, L, R, P):
        try:
            L2, R2, P2 = transformed(L, R, P, *unpack(x, g))
        except np.linalg.LinAlgError:
            return 1e9
        l2, r2 = np.linalg.norm(L2, axis=1), np.linalg.norm(R2, axis=1)
        if kind == "g_2":
            return float(np.sum(l2 * r2 * np.linalg.norm(P2, axis=0)))
        s = np.sqrt(P2 ** 2 + 1e-12) @ (l2 * r2) if kind == "g_inf2" else 0.5 * np.sqrt((P2 ** 2) @ (l2 ** 2 * r2 ** 2))
        m = s.max()
        return float(m + math.log(np.exp(beta * (s - m)).sum()) / beta)
    return f

def task(args):
    L, R, P, g, kind, start, maxiter = args
    rng = np.random.default_rng(1000 * start + 7)
    npar = sum(n * n for n in g)
    x = rng.normal(0, 0.2, npar) if start else np.zeros(npar)
    for beta in (4.0, 16.0, 64.0):
        x = minimize(smooth_obj(kind, beta, g), x, args=(L, R, P), method="L-BFGS-B", options={"maxiter": maxiter}).x
    try:
        L2, R2, P2 = transformed(L, R, P, *unpack(x, g))
    except np.linalg.LinAlgError:
        return kind, start, None
    q = quantities(L2, R2, P2)
    nz = sum(int((np.abs(X) > 1e-6).sum()) for X in (L2, R2, P2))
    return kind, start, (q[kind], q, nz)

def main():
    out, prefix = sys.argv[1], sys.argv[2]
    g = tuple(int(sys.argv[i]) for i in (3, 4, 5))
    def opt(flag, default):
        return int(sys.argv[sys.argv.index(flag) + 1]) if flag in sys.argv else default
    starts, jobs, maxiter = opt("--starts", 8), opt("--jobs", 12), opt("--maxiter", 400)
    L, R, P = (levels.parse_sms(f"{prefix}_{s}.sms") for s in "LRP")
    assert levels.check(L, R, P, g, np.random.default_rng(1))
    q0 = quantities(L, R, P)
    items = [(L, R, P, g, kind, s, maxiter) for kind in ("amp", "g_inf2", "g_2") for s in range(starts)]
    with Pool(jobs) as pool:
        res = pool.map(task, items, chunksize=1)
    best = {}
    for kind, start, r in res:
        if r and (kind not in best or r[0] < best[kind][0]):
            best[kind] = r + (start,)
    cl_amp = 0.5 * math.sqrt(g[1]); total = L.size + R.size + P.size
    with open(out, "w", newline="") as f:
        w = csv.writer(f); w.writerow(["objective", "rep", "min", "start", "at_min", "nnz_of", "total"])
        for kind, (v, q, nz, start) in best.items():
            w.writerow([kind, f"{q0[kind]:.4f}", f"{v:.4f}", start, " ".join(f"{k} {x:.3f}" for k, x in q.items()), nz, total])
    name = os.path.basename(prefix)
    print(f"{name} <{g[0]}x{g[1]}x{g[2]}:{L.shape[0]}>: representative amp {q0['amp']:.3f} (ratio {q0['amp']/cl_amp:.3f}) g_inf2 {q0['g_inf2']:.3f} (ratio {q0['g_inf2']/g[1]:.3f}) g_2 {q0['g_2']:.3f}")
    for kind, (v, q, nz, start) in best.items():
        ratio = v / cl_amp if kind == "amp" else v / g[1] if kind == "g_inf2" else v
        print(f"   {kind:7s} min {v:8.3f} (ratio {ratio:7.3f}) at: " + " ".join(f"{k} {x:.3f}" for k, x in q.items()) + f"; nonzeros {nz}/{total}")

if __name__ == "__main__":
    main()
