#!/usr/bin/env python3
"""Orbit minima of gamma_{inf,2}, amp and gamma_2 for square <n x n x n : r> schemes: L-BFGS over
(U, V, W) in GL_n^3 (3 n^2 parameters, U = I + X) from random starts, every role, smoothed maxima
with continuation in beta, true values and the point's density reported at the optimum.

  python3 -I orbit5.py OUT.csv SPEC [SPEC ...] [--starts 8] [--jobs 12] [--maxiter 300] [--save DIR]
  SPEC = exp:FILE:NAME:n | ae:FILE:FUNC:NAME:n | sms:PREFIX:NAME:n
"""
import csv, math, os, sys
if sys.flags.isolated:
    sys.path.append("/Users/greg/Library/Python/3.9/lib/python/site-packages")
    sys.path.append(os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from multiprocessing import Pool
from scipy.optimize import minimize
import screen5
KINDS = tuple(os.environ.get('KINDS', 'joint').split(','))
TG, TA = float(os.environ.get('TG', '29.7')), float(os.environ.get('TA', '3.26'))

def transformed(L, R, P, U, V, W):
    Ui, Vi, Wi = np.linalg.inv(U), np.linalg.inv(V), np.linalg.inv(W)
    return L @ np.kron(Ui, V.T), R @ np.kron(Vi, W.T), np.kron(U, Wi.T) @ P

def quantities(L, R, P):
    l2, r2 = np.linalg.norm(L, axis=1), np.linalg.norm(R, axis=1)
    s2 = np.abs(P) @ (l2 * r2)
    amp = 0.5 * np.sqrt((P ** 2) @ (l2 ** 2 * r2 ** 2))
    l1, r1 = np.abs(L).sum(1), np.abs(R).sum(1)
    sinf = np.abs(P) @ (l1 * r1)
    return dict(g_inf2=float(s2.max()), amp=float(amp.max()), g_infinf=float(sinf.max()),
                g_22=float(np.linalg.norm(s2)), g_2=float(np.sum(l2 * r2 * np.linalg.norm(P, axis=0))),
                joint=float(max(s2.max() / TG, amp.max() / TA)))

def density(L, R, P, tol=1e-6):
    nz = [np.abs(X) > tol for X in (L, R, P)]
    vals = np.concatenate([np.abs(X[m]) for X, m in zip((L, R, P), nz)])
    return f"nnz {int(nz[0].sum())}/{int(nz[1].sum())}/{int(nz[2].sum())} of {L.size}/{R.size}/{P.size} distinct {len(np.unique(np.round(vals, 6)))}"

def smooth_obj(kind, beta, n):
    def f(x, L, R, P):
        U, V, W = (np.eye(n) + x[k * n * n:(k + 1) * n * n].reshape(n, n) for k in range(3))
        try:
            L2, R2, P2 = transformed(L, R, P, U, V, W)
        except np.linalg.LinAlgError:
            return 1e9
        l2, r2 = np.linalg.norm(L2, axis=1), np.linalg.norm(R2, axis=1)
        if kind == "g_inf2":
            s = np.sqrt(P2 ** 2 + 1e-12) @ (l2 * r2)
        elif kind == "amp":
            s = 0.5 * np.sqrt((P2 ** 2) @ (l2 ** 2 * r2 ** 2))
        elif kind == "joint":   # both thresholds at once: max_j max(s2_j / TG, amp_j / TA) < 1 meets both
            s = np.concatenate([np.sqrt(P2 ** 2 + 1e-12) @ (l2 * r2) / TG, 0.5 * np.sqrt((P2 ** 2) @ (l2 ** 2 * r2 ** 2)) / TA])
        else:
            return float(np.sum(l2 * r2 * np.linalg.norm(P2, axis=0)))
        m = s.max()
        return float(m + math.log(np.exp(beta * (s - m)).sum()) / beta)
    return f

def task(args):
    name, n, role, L, R, P, kind, start, maxiter, save = args
    rng = np.random.default_rng(1000 * start + 7)
    x = rng.normal(0, 0.2, 3 * n * n) if start else np.zeros(3 * n * n)
    for beta in (4.0, 16.0, 64.0):
        r = minimize(smooth_obj(kind, beta, n), x, args=(L, R, P), method="L-BFGS-B", options={"maxiter": maxiter})
        x = r.x
    U, V, W = (np.eye(n) + x[k * n * n:(k + 1) * n * n].reshape(n, n) for k in range(3))
    try:
        L2, R2, P2 = transformed(L, R, P, U, V, W)
    except np.linalg.LinAlgError:
        return (name, role, kind, start, None)
    q = quantities(L2, R2, P2)
    if save:
        np.savez(os.path.join(save, f"{name}_r{role}_{kind}_s{start}.npz"), U=U, V=V, W=W, L=L2, R=R2, P=P2, **q)
    return (name, role, kind, start, (q[kind], q, density(L2, R2, P2)))

def load(spec):
    kind, rest = spec.split(":", 1)
    if kind == "exp":
        f, name, n = rest.rsplit(":", 2); n = int(n); a, b, c = screen5.parse_exp(f, n)
    elif kind == "ae":
        f, func, name, n = rest.rsplit(":", 3); n = int(n); a, b, c = screen5.parse_ae(f, func)
    else:
        f, name, n = rest.rsplit(":", 2); n = int(n)
        L, R, P = (screen5.parse_sms(f"{f}_{s}.sms") for s in "LRP")
        a, b, c = L, R, P.T[:, np.array([n * j + i for i in range(n) for j in range(n)])]
    return name, n, a, b, c

def main():
    args = sys.argv[1:]
    out = args[0]
    def opt(flag, default, cast=int):
        return cast(args[args.index(flag) + 1]) if flag in args else default
    starts, jobs, maxiter, save = opt("--starts", 8), opt("--jobs", 12), opt("--maxiter", 300), opt("--save", None, str)
    if save: os.makedirs(save, exist_ok=True)
    specs = [a for a in args[1:] if ":" in a and not a.startswith("--")]
    rng = np.random.default_rng(1)
    items, reps = [], {}
    for spec in specs:
        name, n, a, b, c = load(spec)
        for role, (x, y, z) in enumerate(((a, b, c), (b, c, a), (c, a, b))):
            t = screen5.to_LRP(x, y, z, n, rng)
            if t is None:
                print(f"{name} role {role}: invalid", flush=True); continue
            L, R, P = t
            reps[(name, role)] = (n, quantities(L, R, P))
            for kind in KINDS:
                for s in range(starts):
                    items.append((name, n, role, L, R, P, kind, s, maxiter, save))
    print(f"{len(items)} tasks on {jobs} processes", flush=True)
    with Pool(jobs) as pool:
        results = pool.map(task, items, chunksize=1)
    best = {}
    for name, role, kind, start, res in results:
        if res is None: continue
        key = (name, role, kind)
        if key not in best or res[0] < best[key][0]:
            best[key] = res + (start,)
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["name", "role", "objective", "rep", "min", "start", "at_min", "density"])
        for (name, role, kind), (v, q, dens, start) in sorted(best.items()):
            w.writerow([name, role, kind, f"{reps[(name, role)][1][kind]:.4f}", f"{v:.4f}", start,
                        " ".join(f"{k} {x:.3f}" for k, x in q.items()), dens])
    for (name, role) in sorted(reps):
        n, q0 = reps[(name, role)]
        Ln = math.log(n); cl = 0.5 * math.sqrt(n)
        line = f"{name:18s} role {role}: "
        for kind in KINDS:
            v = best.get((name, role, kind))
            if v is None: continue
            e = math.log(v[0] / (cl if kind == "amp" else 1)) / Ln
            line += f"{kind} {q0[kind]:8.3f} -> {v[0]:8.3f} (exp {e:.3f})   "
        v = best.get((name, role, "g_inf2"))
        print(line + (f"| at g_inf2 min: {v[2]}" if v else ""), flush=True)

if __name__ == "__main__":
    main()
