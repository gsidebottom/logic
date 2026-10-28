#!/usr/bin/env python3
"""Orbit minima of gamma_{inf,2}, amp and gamma_2 for selected rank-23 3x3 classes: L-BFGS over
(U, V, W) in GL_3^3 (27 parameters) from random starts near the identity, in every role, with
smoothed maxima (log-sum-exp, continuation in beta) and true values reported at the optimum.

  python3 orbit3.py db3_gamma.csv OUT.csv [--top 40] [--starts 8] [--jobs 12]

The stored run (orbit3_minima.csv, orbit3_minima.log) is --top 40 --starts 8 --jobs 12: 124
classes (the union of the top 40 by best g_inf2, amp, g_22 and g_2, plus smirnov and our i19),
about 7 minutes on 12 cores.
"""
import csv
import math
import sys
import os
from multiprocessing import Pool

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import screen3  # noqa: E402

M = screen3.M


def transformed(L, R, P, U, V, W):
    Ui, Vi, Wi = np.linalg.inv(U), np.linalg.inv(V), np.linalg.inv(W)
    return L @ np.kron(Ui, V.T), R @ np.kron(Vi, W.T), np.kron(U, Wi.T) @ P


def check(L, R, P, rng):
    """vec(AB) = P((L vec A) o (R vec B)) for random A, B (row-major)."""
    for _ in range(5):
        A, B = rng.integers(-5, 6, (3, 3)).astype(float), rng.integers(-5, 6, (3, 3)).astype(float)
        got = P @ ((L @ A.reshape(9)) * (R @ B.reshape(9)))
        if not np.allclose(got, (A @ B).reshape(9)):
            return False
    return True


def quantities(L, R, P):
    l2, r2 = np.linalg.norm(L, axis=1), np.linalg.norm(R, axis=1)
    Pt = P  # (9, 23): rows = outputs, columns = products
    s2 = np.abs(Pt) @ (l2 * r2)
    amp = 0.5 * np.sqrt((Pt ** 2) @ (l2 ** 2 * r2 ** 2))
    l1, r1 = np.abs(L).sum(1), np.abs(R).sum(1)
    sinf = np.abs(Pt) @ (l1 * r1)
    g2 = float(np.sum(l2 * r2 * np.linalg.norm(P, axis=0)))
    return dict(g_inf2=float(s2.max()), amp=float(amp.max()), g_infinf=float(sinf.max()), g_22=float(np.linalg.norm(s2)), g_2=g2)


def density(L, R, P, tol=1e-6):
    """How implementable a point is: the nonzeros of L, R and P (each out of 207) and the number
    of distinct absolute coefficients across the three (to six decimals).  A +-1 representative
    has about 150-200 nonzeros and one distinct coefficient."""
    nz = [np.abs(X) > tol for X in (L, R, P)]
    vals = np.concatenate([np.abs(X[m]) for X, m in zip((L, R, P), nz)])
    return f"nnz {int(nz[0].sum())}/{int(nz[1].sum())}/{int(nz[2].sum())} distinct {len(np.unique(np.round(vals, 6)))}"


def smooth_obj(kind, beta):
    def f(x, L, R, P):
        U, V, W = (np.eye(3) + x[k * 9:(k + 1) * 9].reshape(3, 3) for k in range(3))
        try:
            L2, R2, P2 = transformed(L, R, P, U, V, W)
        except np.linalg.LinAlgError:
            return 1e9
        l2, r2 = np.linalg.norm(L2, axis=1), np.linalg.norm(R2, axis=1)
        Pt = P2  # (9, 23)
        if kind == "g_inf2":
            s = np.sqrt(Pt ** 2 + 1e-12) @ (l2 * r2)
        elif kind == "amp":
            s = 0.5 * np.sqrt((Pt ** 2) @ (l2 ** 2 * r2 ** 2))
        else:  # g_2, smooth already
            return float(np.sum(l2 * r2 * np.linalg.norm(P2, axis=0)))
        m = s.max()
        return float(m + math.log(np.exp(beta * (s - m)).sum()) / beta)
    return f


def task(args):
    name, a, b, c, starts = args
    rng = np.random.default_rng(1)
    # convention (HKS .tab, verified on the database): per product the blocks are A, B and C
    # transposed, in row-major order, and every cyclic rotation of the three is again a valid
    # algorithm; so L = x, R = y, P = (z with its 3x3 transposed) as columns.
    T = np.array([3 * j + i for i in range(3) for j in range(3)])  # vec(X^T) = vec(X)[T]
    base = {}
    for role, (x, y, z) in enumerate(((a, b, c), (b, c, a), (c, a, b))):
        L, R, P = x, y, z[:, T].T
        if not check(L, R, P, rng):
            P = None
        base[role] = (L, R, P)
    res = {"name": name}
    for role in range(3):
        L, R, P = base[role]
        if P is None:
            res[f"r{role}_valid"] = 0
            continue
        res[f"r{role}_valid"] = 1
        q0 = quantities(L, R, P)
        for k in ("g_inf2", "amp", "g_2"):
            res[f"r{role}_{k}_rep"] = q0[k]
            best = q0[k]
            bestq = q0
            bestpt = (L, R, P)
            for s in range(starts):
                x = rng.normal(0, 0.25, 27) if s else np.zeros(27)
                for beta in (4.0, 16.0, 64.0):
                    f = smooth_obj(k, beta)
                    r = minimize(f, x, args=(L, R, P), method="L-BFGS-B", options={"maxiter": 200})
                    x = r.x
                U, V, W = (np.eye(3) + x[j * 9:(j + 1) * 9].reshape(3, 3) for j in range(3))
                try:
                    L2, R2, P2 = transformed(L, R, P, U, V, W)
                except np.linalg.LinAlgError:
                    continue
                q = quantities(L2, R2, P2)
                if q[k] < best - 1e-9:
                    best, bestq, bestpt = q[k], q, (L2, R2, P2)
            res[f"r{role}_{k}_min"] = best
            dens = density(*bestpt)
            if k == "g_inf2":
                res[f"r{role}_at_g_inf2_min"] = f"amp {bestq['amp']:.3f} g_infinf {bestq['g_infinf']:.2f} g_22 {bestq['g_22']:.2f} g_2 {bestq['g_2']:.2f} {dens}"
            elif k == "amp":
                res[f"r{role}_at_amp_min"] = f"g_inf2 {bestq['g_inf2']:.3f} g_infinf {bestq['g_infinf']:.2f} g_2 {bestq['g_2']:.2f} {dens}"
            else:
                res[f"r{role}_at_g_2_min"] = f"g_inf2 {bestq['g_inf2']:.3f} amp {bestq['amp']:.3f} {dens}"
    return res


def main():
    screen, out = sys.argv[1], sys.argv[2]
    top = int(sys.argv[sys.argv.index("--top") + 1]) if "--top" in sys.argv else 40
    starts = int(sys.argv[sys.argv.index("--starts") + 1]) if "--starts" in sys.argv else 8
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 12
    rows = list(csv.DictReader(open(screen)))
    db = [r for r in rows if "(ours)" not in r["name"]]
    pick = set()
    for key in ("best_g_inf2", "best_amp", "best_g_22", "g_2"):
        for r in sorted(db, key=lambda r: float(r[key]))[:top]:
            pick.add(r["name"])
    pick.add("smirnov")
    print(f"{len(pick)} classes selected", flush=True)
    items = []
    for name, a, b, c in screen3.load_db():
        if name in pick:
            items.append((name, a, b, c, starts))
    for nm, path in (("i19_55adds (ours)", f"{M}/external/i19-55adds-slp.txt"),):
        a, b, c = screen3.load_slp(path)
        items.append((nm, a, b, c, starts))
    with Pool(jobs) as pool:
        results = pool.map(task, items, chunksize=1)
    keys = sorted({k for r in results for k in r}, key=lambda k: (k != "name", k))
    with open(out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=keys)
        w.writeheader()
        w.writerows(results)
    L3 = math.log(3)

    def best(r, k):
        v = [r[f"r{role}_{k}_min"] for role in range(3) if f"r{role}_{k}_min" in r]
        return min(v) if v else float("nan")

    def dens(r, k):
        roles = [role for role in range(3) if f"r{role}_{k}_min" in r]
        role = min(roles, key=lambda role: r[f"r{role}_{k}_min"])
        s = r[f"r{role}_at_{k}_min"]
        return s[s.index("nnz"):]
    print("\nclass                         g_inf2 rep->min (exp)      amp rep->min (exp)        g_2 rep->min (exp)     point at the g_inf2 min")
    for r in sorted(results, key=lambda r: best(r, "g_inf2")):
        gi = best(r, "g_inf2"); am = best(r, "amp"); g2 = best(r, "g_2")
        gir = min(r[f"r{role}_g_inf2_rep"] for role in range(3) if f"r{role}_g_inf2_rep" in r)
        amr = min(r[f"r{role}_amp_rep"] for role in range(3) if f"r{role}_amp_rep" in r)
        g2r = min(r[f"r{role}_g_2_rep"] for role in range(3) if f"r{role}_g_2_rep" in r)
        print(f"{r['name']:28s} {gir:7.3f}->{gi:7.3f} ({math.log(gi)/L3:.3f})   {amr:6.3f}->{am:6.3f} ({math.log(am/(0.5*math.sqrt(3)))/L3:.3f})   {g2r:6.2f}->{g2:6.2f} ({math.log(g2)/L3:.3f})   {dens(r, 'g_inf2')}")
    print("\nthresholds (accurate_262's exponents): g_inf2 < 11.84 (2.250), amp < 1.974 (0.750), g_2 < 54.29 (3.636)")


if __name__ == "__main__":
    main()
