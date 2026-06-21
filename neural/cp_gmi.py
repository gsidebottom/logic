#!/usr/bin/env python3
"""
Complete CG separator — Gomory cuts from an EXACT rational simplex tableau.

The mod-q separator (cp_lp.fl_separate) is *incomplete*: at the PHP-5-4 stall the
exact any-multiplier F-L MILP still finds violated cuts that no uniform-denominator
mod-q (even Q=LCM) can express, and the float multipliers are un-rationalizable.
The fix (neural_sat_plan.md): produce cuts with **exact rational multipliers by
construction** — Gomory cuts read straight off an optimal simplex tableau.

Pipeline:
  PB system {Σ a·x >= b}  --standard form-->  {Σ a·x - s_j = b_j ; x_v + t_v = 1},
  all vars >= 0  --exact two-phase simplex (Fractions, Bland)-->  optimal tableau.
  A fractional basic row i gives the Gomory cut  Σ_k frac(ā_ik)·y_k >= frac(β_i).
  Reading frac() of the tableau columns gives NONNEGATIVE rational multipliers on
  the original constraints — by column meaning:
      x_v column  -> multiplier on the axiom  x_v >= 0   (literal `x_v`)
      s_j column  -> multiplier on  C_j: Σ a·x >= b      (constraint id j)
      t_v column  -> multiplier on  x_v <= 1 axiom       (literal `~x_v`)
  Scaling by the common denominator D gives integer multipliers; the cut emits as
  the CG step  `pol  Σ λ·Con  D d`  (a divide), exact and veripb-checkable.

Usage:  cp_gmi.py --selftest          # simplex vs scipy, then GMI cuts
        cp_gmi.py --php P H [--verbose]
"""
from __future__ import annotations
import argparse, math, os, sys, tempfile
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cp_search as cp                                    # noqa: E402
import cp_lp                                              # noqa: E402

F0, F1 = Fraction(0), Fraction(1)


# ── PHP instances (UNSAT: P pigeons, H holes, P>H) ──────────────────────────

def php_cnf(P, H, path):
    """Pigeonhole: each pigeon in >=1 hole, each hole holds <=1 pigeon."""
    def var(p, h):
        return p * H + h + 1
    clauses = []
    for p in range(P):                                    # pigeon p in some hole
        clauses.append([var(p, h) for h in range(H)])
    for h in range(H):                                    # hole h: at most one pigeon
        for p1 in range(P):
            for p2 in range(p1 + 1, P):
                clauses.append([-var(p1, h), -var(p2, h)])
    with open(path, "w") as f:
        f.write(f"p cnf {P * H} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
    return path


# ── exact rational simplex ──────────────────────────────────────────────────

class Standard:
    """Standard form  A y = b,  y >= 0  of  {C_j: Σ a·x >= b_j, 0<=x<=1}.

    Columns y = [ x_1..x_n | s_1..s_m | t_1..t_n ]:
        x_v  original var            R_j row:  Σ_v a_jv x_v - s_j = b_j   (s_j>=0)
        s_j  surplus of C_j          U_v row:  x_v + t_v = 1              (t_v>=0)
        t_v  slack of  x_v <= 1
    col_kind[c] = ('x',v) | ('s',j) | ('t',v).  Rows: m R-rows then n U-rows."""

    def __init__(self, constraints, nvars):
        self.cons = list(constraints)
        self.n = nvars
        self.m = len(self.cons)
        m, n = self.m, self.n
        self.ncols = n + m + n
        self.col_kind = ([('x', v) for v in range(1, n + 1)] +
                         [('s', j) for j in range(m)] +
                         [('t', v) for v in range(1, n + 1)])
        # column index helpers
        self.cx = {v: v - 1 for v in range(1, n + 1)}      # x_v -> col
        self.cs = {j: n + j for j in range(m)}             # s_j -> col
        self.ct = {v: n + m + (v - 1) for v in range(1, n + 1)}  # t_v -> col
        # build A (list of rows, Fraction) and b
        A = [[F0] * self.ncols for _ in range(m + n)]
        b = [F0] * (m + n)
        for j, c in enumerate(self.cons):                  # R_j rows
            for v, a in c.coef.items():
                A[j][self.cx[v]] += Fraction(a)
            A[j][self.cs[j]] = Fraction(-1)
            b[j] = Fraction(c.rhs)
        for v in range(1, n + 1):                          # U_v rows
            r = m + (v - 1)
            A[r][self.cx[v]] = F1
            A[r][self.ct[v]] = F1
            b[r] = F1
        self.A, self.b = A, b
        self.nrows = m + n


def _optimize(T, b, basis, cost, ncols):
    """In-place Bland-rule simplex minimizing cost·y on tableau (T,b,basis).
    Returns 'optimal' or 'unbounded'.  cost is a full-length column cost list."""
    nrows = len(basis)
    it = 0
    maxit = 20000 + 200 * (nrows + ncols)
    while True:
        it += 1
        if it > maxit:
            raise RuntimeError("simplex iteration cap (cycling?)")
        cB = [cost[basis[i]] for i in range(nrows)]
        # entering: lowest-index col with negative reduced cost (Bland)
        enter = -1
        for jcol in range(ncols):
            rc = cost[jcol]
            for i in range(nrows):
                if cB[i]:
                    rc -= cB[i] * T[i][jcol]
            if rc < 0:
                enter = jcol
                break
        if enter == -1:
            return "optimal"
        # leaving: min ratio b[i]/T[i][enter] over T[i][enter]>0, Bland tie-break
        leave, best = -1, None
        for i in range(nrows):
            piv = T[i][enter]
            if piv > 0:
                ratio = b[i] / piv
                if (best is None or ratio < best or
                        (ratio == best and basis[i] < basis[leave])):
                    best, leave = ratio, i
        if leave == -1:
            return "unbounded"
        # pivot on (leave, enter)
        piv = T[leave][enter]
        T[leave] = [x / piv for x in T[leave]]
        b[leave] = b[leave] / piv
        for i in range(nrows):
            if i != leave and T[i][enter]:
                f = T[i][enter]
                T[i] = [a - f * c for a, c in zip(T[i], T[leave])]
                b[i] = b[i] - f * b[leave]
        basis[leave] = enter


def solve(std: Standard, obj=None):
    """Two-phase exact simplex.  obj: list over x-columns (default min -Σx, i.e.
    maximize Σx).  Returns (status, T, b, basis) with status in
    {'optimal','infeasible'}.  T/b/basis describe the optimal tableau over the
    STRUCTURAL columns (artificials dropped)."""
    nrows, ncols = std.nrows, std.ncols
    # tableau columns = structural (ncols) + artificials (nrows)
    T = [row[:] + [F0] * nrows for row in std.A]
    b = std.b[:]
    for i in range(nrows):                                 # make rhs >= 0
        if b[i] < 0:
            T[i] = [-x for x in T[i]]
            b[i] = -b[i]
        T[i][ncols + i] = F1                               # artificial a_i
    basis = [ncols + i for i in range(nrows)]
    total = ncols + nrows
    # phase 1: minimize sum of artificials
    cost1 = [F0] * ncols + [F1] * nrows
    _optimize(T, b, basis, cost1, total)
    art_val = sum(b[i] for i in range(nrows) if basis[i] >= ncols)
    if art_val > 0:
        return "infeasible", None, None, None
    # drive any artificial still basic (at 0) out of the basis
    for i in range(nrows):
        if basis[i] >= ncols:
            piv_col = next((j for j in range(ncols) if T[i][j] != 0), -1)
            if piv_col == -1:
                continue                                   # redundant row
            piv = T[i][piv_col]
            T[i] = [x / piv for x in T[i]]
            b[i] = b[i] / piv
            for k in range(nrows):
                if k != i and T[k][piv_col]:
                    f = T[k][piv_col]
                    T[k] = [a - f * c for a, c in zip(T[k], T[i])]
                    b[k] = b[k] - f * b[i]
            basis[i] = piv_col
    # drop redundant rows (artificial still basic at 0 on an all-zero row) and the
    # artificial columns — keeps every basis index a valid structural column
    keep = [i for i in range(nrows) if basis[i] < ncols]
    T = [T[i][:ncols] for i in keep]
    b = [b[i] for i in keep]
    basis = [basis[i] for i in keep]
    # phase 2: optimize real objective
    cost2 = [F0] * ncols
    if obj is None:
        for v in range(1, std.n + 1):
            cost2[std.cx[v]] = Fraction(-1)               # maximize Σx
    else:
        for v in range(1, std.n + 1):
            cost2[std.cx[v]] = Fraction(obj[v - 1])
    _optimize(T, b, basis, cost2, ncols)
    return "optimal", T, b, basis


def primal(std: Standard, b, basis):
    """x* (length n, Fractions) from an optimal tableau."""
    x = [F0] * std.n
    pos = {basis[i]: i for i in range(len(basis))}
    for v in range(1, std.n + 1):
        c = std.cx[v]
        if c in pos:
            x[v - 1] = b[pos[c]]
    return x


# ── Gomory cuts from the optimal tableau ────────────────────────────────────

def _frac(z: Fraction) -> Fraction:
    return z - math.floor(z)


def _lcm(a, b):
    return a * b // math.gcd(a, b)


def build_cut(std: Standard, lamC, lamL, lamB, D):
    """Realize the CG cut  divide( Σ λC·C_j + Σ λL·(x_v>=0) + Σ λB·(~x_v>=0), D )
    using the SAME PB ops veripb will replay, so the returned PB is exactly what
    the emitted `pol` derives.  λ* are nonneg ints, D>0."""
    terms = []
    for j, lam in lamC.items():
        c = std.cons[j]
        terms.append(cp.PB({v: a * lam for v, a in c.coef.items()}, c.rhs * lam))
    for v, lam in lamL.items():
        terms.append(cp.PB({v: lam}, 0))                  # λ·(x_v >= 0)
    for v, lam in lamB.items():
        terms.append(cp.PB({v: -lam}, -lam))              # λ·(1 - x_v >= 0)
    G = terms[0]
    for t in terms[1:]:
        G = cp.add_scaled(G, 1, t, 1)
    return cp.divide(G.norm(), D)


def gomory_cuts(std: Standard, T, b, basis, x):
    """All distinct violated Gomory cuts from the fractional basic rows.  Returns
    [(viol, cut_pb, recipe)] with recipe = (D, lamC, lamL, lamB) (int multipliers,
    keyed by cons-index / var) — the pol emission recipe."""
    out, seen = [], set()
    for i in range(len(basis)):
        if _frac(b[i]) == 0:                              # integral basic value
            continue
        row = T[i]
        # rational multipliers = frac of the tableau entry, by column meaning
        fL = {v: _frac(row[std.cx[v]]) for v in range(1, std.n + 1)}
        fC = {j: _frac(row[std.cs[j]]) for j in range(std.m)}
        fB = {v: _frac(row[std.ct[v]]) for v in range(1, std.n + 1)}
        fL = {v: f for v, f in fL.items() if f}
        fC = {j: f for j, f in fC.items() if f}
        fB = {v: f for v, f in fB.items() if f}
        D = 1
        for f in list(fL.values()) + list(fC.values()) + list(fB.values()):
            D = _lcm(D, f.denominator)
        if D == 1:                                        # no fractional column
            continue
        lamL = {v: int(f * D) for v, f in fL.items()}
        lamC = {j: int(f * D) for j, f in fC.items()}
        lamB = {v: int(f * D) for v, f in fB.items()}
        cut = build_cut(std, lamC, lamL, lamB, D)
        if not cut.coef:
            continue
        viol = cut.rhs - sum(cut.coef.get(v, 0) * x[v - 1] for v in cut.coef)
        if viol <= 0:
            continue
        k = cut.canonical().key()
        if k in seen:
            continue
        seen.add(k)
        out.append((viol, cut, (D, lamC, lamL, lamB)))
    out.sort(key=lambda t: -t[0])
    return out


def gmi_loop(constraints, nvars, max_rounds=80, n_obj=4, seed=0, verbose=False,
             max_secs=300, max_cuts_round=0):
    """Cutting-plane loop with Gomory separation.  Each round re-solves the exact
    LP under n_obj rotated objectives, exposing fractional vertices, and adds the
    distinct violated Gomory cuts.  Returns (cons, refuted, cut_recipes)."""
    import time
    import numpy as np
    cons = list(constraints)
    cut_recipes = []
    seen = {c.canonical().key() for c in cons}
    rng = np.random.default_rng(seed)
    t0 = time.time()
    for rnd in range(max_rounds):
        if time.time() - t0 > max_secs:
            if verbose:
                print(f"    timeout after {rnd} rounds ({len(cut_recipes)} cuts)")
            return cons, False, cut_recipes
        objs = [None] + [list(rng.uniform(-1, 1, nvars)) for _ in range(n_obj - 1)]
        added = 0
        for obj in objs:
            std = Standard(cons, nvars)
            status, T, b, basis = solve(std, obj)
            if status == "infeasible":
                if verbose:
                    print(f"    round {rnd}: LP infeasible — refuted "
                          f"({len(cut_recipes)} cuts)")
                return cons, True, cut_recipes
            x = primal(std, b, basis)
            cuts = gomory_cuts(std, T, b, basis, x)
            if max_cuts_round:
                cuts = cuts[:max_cuts_round]
            for viol, cut, recipe in cuts:
                k = cut.canonical().key()
                if k in seen:
                    continue
                seen.add(k)
                cons.append(cut)
                cut_recipes.append(recipe)
                added += 1
        if verbose:
            print(f"    round {rnd}: +{added} cuts (total {len(cut_recipes)})")
        if added == 0:
            return cons, False, cut_recipes
    return cons, False, cut_recipes


# ── emission ────────────────────────────────────────────────────────────────

def _pol_terms(terms, suffix):
    """Reverse-polish for  Σ (ref·λ)  followed by `suffix` tokens."""
    rp, first = [], True
    for ref, lam in terms:
        rp += [ref, str(lam), "*"]
        if not first:
            rp.append("+")
        first = False
    return "pol " + " ".join(rp + suffix) + " ;"


def emit_gmi(n_inputs, cut_recipes, mult, path):
    """Emit the GMI proof: each Gomory cut as a CG `pol Σ λ·Con  D d` (Con = a
    constraint id, the axiom `x_v` (x_v>=0) or `~x_v` (x_v<=1)), then the final
    Farkas combination.  cut_recipes[k] lives at constraint id n_inputs+1+k."""
    lines = ["pseudo-Boolean proof version 3.0", f"f {n_inputs};"]
    for (D, lamC, lamL, lamB) in cut_recipes:
        terms = [(str(j + 1), lamC[j]) for j in sorted(lamC)]
        terms += [(f"x{v}", lamL[v]) for v in sorted(lamL)]
        terms += [(f"~x{v}", lamB[v]) for v in sorted(lamB)]
        lines.append(_pol_terms(terms, [str(D), "d"]))
    terms = [(str(j + 1), mult[j]) for j in range(len(mult)) if mult[j]]
    lines.append(_pol_terms(terms, []))
    lines += ["output NONE;", "conclusion UNSAT : -1;", "end pseudo-Boolean proof;"]
    open(path, "w").write("\n".join(lines) + "\n")


def refute_gmi(cnf_path, verbose=False, **kw):
    inputs = cp.read_cnf(cnf_path)
    nvars = max((v for c in inputs for v in c.coef), default=0)
    cons, refuted, cut_recipes = gmi_loop(inputs, nvars, verbose=verbose, **kw)
    if not refuted:
        print(f"  not refuted by Gomory cuts ({len(cut_recipes)} cuts added)")
        return False
    mult = cp_lp.farkas_refute(cons)
    if not mult:
        print(f"  {len(cut_recipes)} cuts added but final Farkas failed")
        return False
    pbp = cnf_path + ".gmi.pbp"
    emit_gmi(len(inputs), cut_recipes, mult, pbp)
    ok, tail = cp.verify(cnf_path, pbp)
    print(f"  GMI: {len(cut_recipes)} Gomory cuts + Farkas  ->  veripb: "
          f"{'VERIFIED' if ok else 'FAILED ' + str(tail)}")
    return ok


# ── self-test: simplex vs scipy ─────────────────────────────────────────────

def _selftest_simplex():
    import numpy as np
    from scipy.optimize import linprog
    rng = np.random.default_rng(0)
    ok = True
    cases = 0
    for trial in range(40):
        n = int(rng.integers(2, 5))
        m = int(rng.integers(1, 6))
        cons = []
        for _ in range(m):
            k = int(rng.integers(1, n + 1))
            vs = rng.choice(range(1, n + 1), size=k, replace=False)
            coef = {int(v): int(rng.integers(-2, 3)) for v in vs}
            coef = {v: a for v, a in coef.items() if a != 0}
            if not coef:
                continue
            rhs = int(rng.integers(-2, 3))
            cons.append(cp.PB(coef, rhs))
        if not cons:
            continue
        objc = [float(rng.uniform(-1, 1)) for _ in range(n)]
        std = Standard(cons, n)
        status, T, b, basis = solve(std, obj=objc)
        # scipy reference
        A_ub = [[-float(c.coef.get(v, 0)) for v in range(1, n + 1)] for c in cons]
        b_ub = [-float(c.rhs) for c in cons]
        res = linprog(objc, A_ub=A_ub, b_ub=b_ub, bounds=[(0, 1)] * n,
                      method="highs")
        cases += 1
        if status == "infeasible":
            if res.status != 2:
                print(f"  trial {trial}: simplex infeasible, scipy status "
                      f"{res.status}"); ok = False
            continue
        if res.status == 2:
            print(f"  trial {trial}: simplex optimal, scipy infeasible"); ok = False
            continue
        x = primal(std, b, basis)
        val = sum(Fraction(objc[v]).limit_denominator(10**9) * x[v]
                  for v in range(n))
        # feasibility of x*
        feas = all(sum(c.coef.get(v, 0) * x[v - 1] for v in c.coef) >= c.rhs
                   for c in cons) and all(F0 <= xi <= F1 for xi in x)
        if not feas:
            print(f"  trial {trial}: x* infeasible {x}"); ok = False
        if abs(float(val) - res.fun) > 1e-6:
            print(f"  trial {trial}: obj mismatch exact={float(val):.6f} "
                  f"scipy={res.fun:.6f}"); ok = False
    print(f"SIMPLEX vs scipy: {cases} cases, {'PASS' if ok else 'FAIL'}")
    return ok


def _selftest_gmi():
    """End-to-end: refute small PHP families, each veripb-VERIFIED."""
    td = tempfile.mkdtemp(prefix="gmi_")
    ok = True
    for P, H in [(3, 2), (4, 3), (5, 4)]:
        path = php_cnf(P, H, os.path.join(td, f"php_{P}_{H}.cnf"))
        print(f"[PHP-{P}-{H}]")
        ok &= refute_gmi(path, max_secs=120)
    print("GMI end-to-end:", "PASS" if ok else "FAIL")
    return ok


def selftest():
    ok = _selftest_simplex()
    ok &= _selftest_gmi()
    print("SELFTEST", "PASS" if ok else "FAIL")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--php", nargs=2, type=int, metavar=("P", "H"))
    ap.add_argument("--cnf")
    ap.add_argument("--max-rounds", type=int, default=80)
    ap.add_argument("--n-obj", type=int, default=4)
    ap.add_argument("--max-secs", type=float, default=300)
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        sys.exit(0 if selftest() else 1)
    kw = dict(max_rounds=args.max_rounds, n_obj=args.n_obj, max_secs=args.max_secs,
              verbose=args.verbose)
    if args.php:
        P, H = args.php
        td = tempfile.mkdtemp(prefix=f"php_{P}_{H}_")
        path = php_cnf(P, H, os.path.join(td, f"php_{P}_{H}.cnf"))
        print(f"[PHP-{P}-{H}]  ({P} pigeons, {H} holes)")
        refute_gmi(path, **kw)
    elif args.cnf:
        print(f"[{os.path.basename(args.cnf)}]")
        refute_gmi(args.cnf, **kw)


if __name__ == "__main__":
    main()
