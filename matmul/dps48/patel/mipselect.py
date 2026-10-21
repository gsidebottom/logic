#!/opt/homebrew/bin/python3
"""Experiment 3e prototype: exact repair for the value-set LNS.

On an enlarged dictionary (the current program's signal set plus a batch of
proposals drawn with Patel's six families), compare
  * the greedy reverse deletion (Patel's repair, several random orders) with
  * the exact minimum closed subset, solved as a MIP (scipy.optimize.milp /
    HiGHS): x_v selects vector v, y_p selects production p of v (both operands
    selected), sum_p y_p >= x_v, inputs and targets fixed, acyclicity by
    continuous levels with a big-M on each selected production.
Cost = number of selected non-input vectors (PLinOpt's objective, negations
free).  Reports both costs per trial, and whether the MIP's set is closed.

Usage: mipselect.py --slp PROG.slp [--n 16] [--trials 10] [--k 40] [--seed 1]
       [--time 120] [--orders 8]          (PATEL_SEARCH must point at his search/)
"""
import argparse
import os
import random
import sys
import time

import numpy as np
from scipy.optimize import LinearConstraint, Bounds, milp
from scipy.sparse import coo_matrix

SEARCH = os.environ.get("PATEL_SEARCH", os.path.expanduser("~/src/matmul-4x4-48-202/search"))
sys.path.insert(0, SEARCH)
import rebuild  # noqa: E402
import rebuild2  # noqa: E402
import slp  # noqa: E402


def bits(mask):
    return list(rebuild.bits(mask))


def mip_select(catalog, time_limit):
    """minimum closed subset of the dictionary containing inputs and targets."""
    pool = catalog.pool
    D = len(pool.values)
    n = pool.n
    # productions: (v, u, w or -1)
    prods = []
    for v in range(n, D):
        for (u, w, a, b) in catalog.options[v]:
            prods.append((v, u, w))
    P = len(prods)
    # variables: x_0..x_{D-1}, y_0..y_{P-1}, l_0..l_{D-1}
    nx, ny, nl = D, P, D
    nvar = nx + ny + nl
    c = np.zeros(nvar)
    c[n:D] = 1.0  # minimize selected non-inputs
    lb = np.zeros(nvar)
    ub = np.ones(nvar)
    integrality = np.zeros(nvar)
    integrality[:nx + ny] = 1
    lb[:n] = 1.0  # inputs selected
    for i in range(D):
        if (pool.required >> i) & 1:
            lb[i] = 1.0  # targets selected
    ub[nx + ny:] = D  # levels
    ub[nx + ny:nx + ny + n] = 0  # inputs at level 0
    rows, cols, vals, lo, hi = [], [], [], [], []
    r = 0
    M = D + 1
    for pi, (v, u, w) in enumerate(prods):
        yv = nx + pi
        # y_p <= x_u
        rows += [r, r]; cols += [yv, u]; vals += [1.0, -1.0]; lo.append(-np.inf); hi.append(0.0); r += 1
        if w >= 0:
            rows += [r, r]; cols += [yv, w]; vals += [1.0, -1.0]; lo.append(-np.inf); hi.append(0.0); r += 1
        # l_v >= l_u + 1 - M (1 - y_p)  <=>  l_v - l_u - M y_p >= 1 - M
        rows += [r, r, r]; cols += [nx + ny + v, nx + ny + u, yv]; vals += [1.0, -1.0, -M]; lo.append(1.0 - M); hi.append(np.inf); r += 1
        if w >= 0:
            rows += [r, r, r]; cols += [nx + ny + v, nx + ny + w, yv]; vals += [1.0, -1.0, -M]; lo.append(1.0 - M); hi.append(np.inf); r += 1
    # sum_p y_p >= x_v for each non-input v
    by_v = {}
    for pi, (v, u, w) in enumerate(prods):
        by_v.setdefault(v, []).append(pi)
    for v in range(n, D):
        ps = by_v.get(v, [])
        for pi in ps:
            rows.append(r); cols.append(nx + pi); vals.append(1.0)
        rows.append(r); cols.append(v); vals.append(-1.0)
        lo.append(0.0); hi.append(np.inf); r += 1
    A = coo_matrix((vals, (rows, cols)), shape=(r, nvar)).tocsr()
    res = milp(c, constraints=LinearConstraint(A, lo, hi), integrality=integrality, bounds=Bounds(lb, ub),
               options={"time_limit": time_limit, "disp": False})
    if res.x is None:
        return None, res.status, None
    sel = 0
    for i in range(D):
        if res.x[i] > 0.5:
            sel |= 1 << i
    cost = int(round(res.fun))
    return cost, res.status, sel


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--slp", required=True)
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--trials", type=int, default=10)
    ap.add_argument("--k", type=int, default=40, help="proposals per trial")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--time", type=float, default=120)
    ap.add_argument("--orders", type=int, default=8)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    prog = slp.parse_slp(a.slp)
    pool0 = rebuild.Dictionary.from_program(prog, a.n)
    base_cost = len(pool0.values) - a.n
    targets = [tuple(s * x for x in pool0.values[i]) for i, s in pool0.targets]
    print(f"program: {slp.count_ops(prog)} -> {base_cost} distinct non-input signals; {len(pool0.targets)} targets", flush=True)
    props = rebuild2.Proposals(prog, a.n)
    values0 = list(pool0.values)
    for t in range(a.trials):
        t0 = time.time()
        values = list(values0)
        proposals = []
        while len(proposals) < a.k:
            new, fams = props.draw(values, rng, min(8, a.k - len(proposals)))
            proposals += new
            values = values0 + proposals
        pool = rebuild.Dictionary(a.n, values0 + proposals, targets)
        cat = rebuild2.Catalog(pool)
        full = pool.full
        assert cat.closure(full)
        # greedy reverse deletion (no z3: cost = popcount - n)
        best = None
        for _ in range(a.orders):
            sel = full
            changed = True
            while changed:
                changed = False
                removable = bits(sel & ~pool.required)
                rng.shuffle(removable)
                for x in removable:
                    trial = sel & ~(1 << x)
                    if cat.closure(trial):
                        sel = trial
                        changed = True
            cst = bin(sel).count("1") - a.n
            if best is None or cst < best:
                best = cst
        t1 = time.time()
        mcost, status, msel = mip_select(cat, a.time)
        t2 = time.time()
        closed = cat.closure(msel) if msel is not None else None
        print(f"trial {t + 1}: dictionary {len(pool.values)} vectors ({len(proposals)} proposals, {cat.count} productions); "
              f"greedy best {best} ({t1 - t0:.1f}s); MIP {mcost} status {status} closed {closed} ({t2 - t1:.1f}s)"
              f"{'  <-- MIP BETTER' if mcost is not None and mcost < best else ''}", flush=True)


if __name__ == "__main__":
    main()
