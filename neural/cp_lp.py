#!/usr/bin/env python3
"""
LP-guided cutting-plane engine — Phase A: signed-variable Farkas refutation.

The blind best-first FM search (cp_search.py) generates millions of constraints
to find a tiny proof.  The principled engine is goal-directed: an UNSAT
PB/clausal system is LP-infeasible (eventually, after CG cuts), and Farkas'
lemma gives the *exact* nonnegative combination of constraints that collapses to
0 >= positive — which is precisely a VeriPB `pol` proof.

Phase A handles systems already infeasible over the reals (no cuts needed):
find y >= 0 with  Σ_j y_j · coef_j[i] = 0  for every variable i  and
Σ_j y_j · rhs_j > 0  (LP), rationalize y to integer multipliers, and emit
`pol Σ m_j·C_j` → 0 >= positive, checked by VeriPB.  (Phase B adds the CG-cut
loop for LP-feasible-but-UNSAT systems like PHP.)

Usage:  cp_lp.py --selftest
        cp_lp.py --cnf foo.cnf
"""
from __future__ import annotations
import argparse, os, sys, tempfile
from fractions import Fraction
from math import gcd
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cp_search as cp                                  # noqa: E402


def farkas_refute(constraints):
    """Integer multipliers proving infeasibility-over-R, or None.

    LP: maximize Σ y_j rhs_j  s.t.  Σ_j y_j coef_j[i] = 0 ∀i,  y >= 0,  Σ y <= 1
    (the last normalizes the Farkas ray).  >0 optimum ⇒ a certificate."""
    m = len(constraints)
    if m == 0:
        return None
    varset = sorted({v for c in constraints for v in c.coef})
    A_eq = [[c.coef.get(v, 0) for c in constraints] for v in varset] or None
    b_eq = [0] * len(varset) or None
    obj = [-c.rhs for c in constraints]                 # minimize -Σ y rhs
    res = linprog(obj, A_ub=[[1.0] * m], b_ub=[1.0], A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0, None)] * m, method="highs")
    if not res.success or -res.fun <= 1e-7:
        return None
    # rationalize the ray → integer multipliers
    fr = [Fraction(v).limit_denominator(10 ** 6) if v > 1e-9 else Fraction(0)
          for v in res.x]
    lcm = 1
    for f in fr:
        if f:
            lcm = lcm * f.denominator // gcd(lcm, f.denominator)
    mult = [int(f * lcm) for f in fr]
    g = 0
    for mi in mult:
        g = gcd(g, mi)
    if g > 1:
        mult = [mi // g for mi in mult]
    # verify EXACTLY (float LP must yield exact integer cancellation)
    acc = None
    for j, mj in enumerate(mult):
        if mj == 0:
            continue
        term = cp.PB({v: c * mj for v, c in constraints[j].coef.items()},
                     constraints[j].rhs * mj)
        acc = term if acc is None else cp.add_scaled(acc, 1, term, 1)
    if acc is None:
        return None
    acc = acc.norm()
    if acc.coef or acc.rhs < 1:                         # not a clean 0 >= positive
        return None
    return mult


def lp_point(constraints, nvars, obj=None):
    """Optimize a linear objective (default: maximize Σ x) over
    {coef·x >= rhs, 0<=x<=1}.  Returns (status, x*): status 'infeasible' ⇒ refuted;
    else x* is a fractional vertex to separate.  Rotating obj exposes different
    vertices — essential to avoid cutting-plane stalling on a single vertex."""
    A_ub, b_ub = [], []
    for c in constraints:
        row = [0.0] * nvars
        for v, a in c.coef.items():
            row[v - 1] = -float(a)                       # coef·x>=rhs  ⇔  -coef·x<=-rhs
        A_ub.append(row); b_ub.append(-float(c.rhs))
    c_obj = [-1.0] * nvars if obj is None else list(obj)  # default: maximize Σx
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub,
                  bounds=[(0, 1)] * nvars, method="highs")
    if res.status == 2:
        return "infeasible", None
    if res.status == 0:
        return "feasible", res.x
    return "unknown", None


def gf2_nullspace(A):
    """Basis of the GF(2) null space of A (rows=vars, cols=constraints): 0/1
    column-combinations with all-even variable coefficients."""
    A = (A.copy() % 2); m, n = A.shape
    pivots, r = [], 0
    for col in range(n):
        piv = next((i for i in range(r, m) if A[i, col]), None)
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, col]:
                A[i] = (A[i] + A[r]) % 2
        pivots.append(col); r += 1
        if r == m:
            break
    pset = set(pivots)
    basis = []
    for f in (c for c in range(n) if c not in pset):
        vec = np.zeros(n, dtype=int); vec[f] = 1
        for ri, pc in enumerate(pivots):
            if A[ri, f]:
                vec[pc] = 1
        basis.append(vec)
    return basis


def mod2_cuts(constraints, nvars, x):
    """Separate {0,1/2}-Chvátal-Gomory cuts violated by x*.  A cut = (1/2)·Σ_T C_j
    rounded, where T is a GF(2) null-space combo (even coeffs) with odd degree."""
    var_idx = {v: i for i, v in enumerate(sorted({v for c in constraints
                                                  for v in c.coef}))}
    A = np.zeros((len(var_idx), len(constraints)), dtype=int)
    for j, c in enumerate(constraints):
        for v, a in c.coef.items():
            A[var_idx[v], j] = a % 2
    deg = np.array([c.rhs % 2 for c in constraints])
    basis = gf2_nullspace(A)
    # candidate combos: single basis vectors + pairwise XORs (keep it bounded)
    cand = list(basis) + [(basis[i] ^ basis[k]) for i in range(len(basis))
                          for k in range(i + 1, min(len(basis), i + 12))]
    cuts = []
    seen = set()
    for t in cand:
        if (deg @ t) % 2 != 1:                           # need odd degree to round
            continue
        sel = [j for j in range(len(constraints)) if t[j]]
        if not (2 <= len(sel) <= 40):
            continue
        combo = None
        for j in sel:
            term = constraints[j]
            combo = cp.PB(dict(term.coef), term.rhs) if combo is None \
                else cp.add_scaled(combo, 1, term, 1)
        combo = combo.norm()
        cut = cp.divide(combo, 2)                        # CG round
        viol = cut.rhs - sum(cut.coef.get(v, 0) * x[v - 1] for v in cut.coef)
        if viol > 1e-6:
            k = cut.canonical().key()
            if k not in seen:
                seen.add(k); cuts.append((viol, {j: 1 for j in sel}, 2, cut))
    cuts.sort(key=lambda t: -t[0])
    return cuts


def _modq_separate(constraints, Ap, bp, xs, varset, x, q):
    """Most-violated CG cut with a FIXED divisor q: integer multipliers
    w_j ∈ {0..q-1}, cut coeffs ⌊(Σ w_j A'_ji)/q⌋.  Integer-only MILP → the cut is
    exact and emits cleanly as `pol Σ w_j·C_j q d` (no float rationalization)."""
    m, n = len(constraints), len(varset)
    iw, ia, ir, izb, irb = 0, m, m + n, m + 2 * n, m + 2 * n + 1
    N = m + 2 * n + 2
    c_obj = np.zeros(N)                                     # max Σ alpha·x* - zb
    for i in range(n):
        c_obj[ia + i] = -xs[i]
    c_obj[izb] = 1.0
    Aeq = np.zeros((n + 1, N))
    for i in range(n):                                     # A'w - q·alpha - r = 0
        Aeq[i, iw:iw + m] = Ap[i]; Aeq[i, ia + i] = -q; Aeq[i, ir + i] = -1.0
    Aeq[n, iw:iw + m] = bp; Aeq[n, izb] = -q; Aeq[n, irb] = -1.0  # b'w - q·zb - rb = 0
    AMAX = float(np.abs(Ap).sum() + np.abs(bp).sum() + 10)
    lo = np.zeros(N); hi = np.zeros(N)
    hi[iw:iw + m] = q - 1; hi[ir:ir + n] = q - 1; hi[irb] = q - 1
    lo[ia:ia + n] = -AMAX; hi[ia:ia + n] = AMAX; lo[izb] = -AMAX; hi[izb] = AMAX
    res = milp(c_obj, constraints=LinearConstraint(Aeq, np.zeros(n + 1), np.zeros(n + 1)),
               integrality=np.ones(N), bounds=Bounds(lo, hi),
               options={"time_limit": 5.0})           # bound each separation MILP
    if not res.success or res.fun is None or -res.fun <= 1e-6:
        return None
    w = np.round(res.x[iw:iw + m]).astype(int)
    mults = {j: int(w[j]) for j in range(m) if w[j] > 0}
    if not mults:
        return None
    combo = None
    for j, mj in mults.items():
        term = cp.PB({v: a * mj for v, a in constraints[j].coef.items()},
                     constraints[j].rhs * mj)
        combo = term if combo is None else cp.add_scaled(combo, 1, term, 1)
    cut = cp.divide(combo.norm(), q)
    viol = cut.rhs - sum(cut.coef.get(v, 0) * x[v - 1] for v in cut.coef)
    return (viol, mults, q, cut) if viol > 1e-6 else None


def fl_separate(constraints, nvars, x, qs=(2, 3, 4, 5, 6)):
    """General CG separation: sweep small fixed divisors q and return the
    most-violated cut found (Fischetti–Lodi style, but integer-multiplier per q so
    cuts are exact + emittable).  Returns (viol, mults, q, cut) or None."""
    varset = sorted({v for c in constraints for v in c.coef})
    n, m = len(varset), len(constraints)
    vi = {v: i for i, v in enumerate(varset)}
    Ap = np.zeros((n, m)); bp = np.zeros(m)                 # <=-form: A'=-coef, b'=-rhs
    for j, c in enumerate(constraints):
        for v, a in c.coef.items():
            Ap[vi[v], j] = -a
        bp[j] = -c.rhs
    xs = np.array([x[v - 1] for v in varset])
    best = None
    for q in qs:
        r = _modq_separate(constraints, Ap, bp, xs, varset, x, q)
        if r and (best is None or r[0] > best[0]):
            best = r
    return best


def separate_all(constraints, nvars, x, qmax=10):
    """All distinct violated CG cuts at x*: the cheap {0,1/2} (GF(2)) batch plus the
    best mod-q cut for each divisor q=3..qmax.  Returns [(viol, mults, q, cut)]."""
    cuts = list(mod2_cuts(constraints, nvars, x))         # many q=2 cuts (no MILP)
    if qmax >= 3:
        varset = sorted({v for c in constraints for v in c.coef})
        n, m = len(varset), len(constraints)
        vi = {v: i for i, v in enumerate(varset)}
        Ap = np.zeros((n, m)); bp = np.zeros(m)
        for j, c in enumerate(constraints):
            for v, a in c.coef.items():
                Ap[vi[v], j] = -a
            bp[j] = -c.rhs
        xs = np.array([x[v - 1] for v in varset])
        for q in range(3, qmax + 1):
            r = _modq_separate(constraints, Ap, bp, xs, varset, x, q)
            if r:
                cuts.append(r)
    return cuts


def cg_loop(constraints, nvars, max_rounds=40, qmax=10, n_obj=6, seed=0,
            verbose=False):
    """Cutting-plane loop → Farkas.  Each round rotates n_obj LP objectives (to
    expose different vertices) and adds ALL distinct violated CG cuts found across
    the q=2..qmax sweep.  Single-vertex / single-best-cut separation stalls before
    infeasibility; rotation + add-all drives the LP infeasible.  Returns
    (cons, refuted, cut_derivs) with cut_derivs[k]=(mults, q): the k-th cut is
    `divide(Σ mults[j]·C_j, q)`, the pol emission recipe."""
    cons = list(constraints)
    cut_derivs = []
    seen = {c.canonical().key() for c in cons}
    rng = np.random.default_rng(seed)
    for rnd in range(max_rounds):
        objs = [None] + [list(rng.uniform(-1, 1, nvars)) for _ in range(n_obj - 1)]
        added = 0
        for obj in objs:
            status, x = lp_point(cons, nvars, obj)
            if status == "infeasible":
                if verbose:
                    print(f"    round {rnd}: LP infeasible — refuted "
                          f"({len(cut_derivs)} cuts)")
                return cons, True, cut_derivs
            if status != "feasible":
                continue
            for _, mults, q, cut in separate_all(cons, nvars, x, qmax):
                k = cut.canonical().key()
                if k in seen:
                    continue
                seen.add(k); cut_derivs.append((mults, q)); cons.append(cut)
                added += 1
        if verbose:
            print(f"    round {rnd}: +{added} cuts (total {len(cut_derivs)})")
        if added == 0:
            return cons, False, cut_derivs
    return cons, False, cut_derivs


def emit_cg(n_inputs, cut_derivs, mult, path):
    """Emit the LP-CG proof: each cut as `pol <Σ sel> 2 d`, then the final Farkas
    `pol Σ m_j·C_j` over inputs+cuts (constraint at index i → veripb id i+1)."""
    lines = ["pseudo-Boolean proof version 3.0", f"f {n_inputs};"]
    for mults, q in cut_derivs:
        items = sorted(mults.items())                     # (constraint index, m_j)
        rp, first = [], True
        for idx, mj in items:
            rp += [str(idx + 1), str(mj), "*"]
            if not first:
                rp.append("+")
            first = False
        rp += [str(q), "d"]                               # CG divide by q
        lines.append("pol " + " ".join(rp) + " ;")
    rp, first = [], True
    for j, mj in enumerate(mult):
        if mj == 0:
            continue
        rp += [str(j + 1), str(mj), "*"]
        if not first:
            rp.append("+")
        first = False
    lines.append("pol " + " ".join(rp) + " ;")
    lines += ["output NONE;", "conclusion UNSAT : -1;", "end pseudo-Boolean proof;"]
    open(path, "w").write("\n".join(lines) + "\n")


def refute_cg(cnf_path, verbose=False):
    inputs = cp.read_cnf(cnf_path)
    nvars = max((v for c in inputs for v in c.coef), default=0)
    cons, refuted, cut_derivs = cg_loop(inputs, nvars, verbose=verbose)
    if not refuted:
        print(f"  not refuted by CG cuts ({len(cut_derivs)} cuts added)")
        return False
    mult = farkas_refute(cons)
    if not mult:
        print(f"  {len(cut_derivs)} cuts added but final Farkas failed")
        return False
    pbp = cnf_path + ".cg.pbp"
    emit_cg(len(inputs), cut_derivs, mult, pbp)
    ok, tail = cp.verify(cnf_path, pbp)
    print(f"  LP-CG: {len(cut_derivs)} cuts + Farkas  ->  veripb: "
          f"{'VERIFIED' if ok else 'FAILED ' + str(tail)}")
    return ok


def emit_farkas(n_inputs, mult, path):
    """Emit `pol Σ m_j·C_j` over input constraints (ids 1..n_inputs)."""
    rp, first = [], True
    for j, mj in enumerate(mult):
        if mj == 0:
            continue
        rp += [str(j + 1), str(mj), "*"]
        if not first:
            rp.append("+")
        first = False
    lines = ["pseudo-Boolean proof version 3.0", f"f {n_inputs};",
             "pol " + " ".join(rp) + " ;",
             "output NONE;", "conclusion UNSAT : -1;", "end pseudo-Boolean proof;"]
    open(path, "w").write("\n".join(lines) + "\n")


def refute_cnf(cnf_path):
    inputs = cp.read_cnf(cnf_path)
    mult = farkas_refute(inputs)
    if not mult:
        print("  no Farkas refutation (LP-feasible over R — needs CG cuts, Phase B)")
        return False
    pbp = cnf_path + ".lp.pbp"
    emit_farkas(len(inputs), mult, pbp)
    ok, tail = cp.verify(cnf_path, pbp)
    nz = sum(1 for mi in mult if mi)
    print(f"  Farkas: {nz} constraints combined (mults "
          f"{[m for m in mult if m]})  ->  veripb: "
          f"{'VERIFIED' if ok else 'FAILED ' + str(tail)}")
    return ok


def selftest():
    td = tempfile.mkdtemp(prefix="cplp_")
    cases = {
        "lp_infeasible": "p cnf 2 3\n1 2 0\n1 -2 0\n-1 0\n",        # mults (1,1,2)
        "amo3": "p cnf 2 3\n1 0\n2 0\n-1 -2 0\n",                   # x,y, ~x∨~y
        "chain": "p cnf 3 4\n1 0\n-1 2 0\n-2 3 0\n-3 0\n",          # x, x→y, y→z, ¬z
    }
    allok = True
    for name, cnf in cases.items():
        p = os.path.join(td, name + ".cnf"); open(p, "w").write(cnf)
        print(f"[{name}]"); allok &= refute_cnf(p)
    print("SELFTEST", "PASS" if allok else "FAIL")
    return allok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--cnf")
    ap.add_argument("--cg", action="store_true",
                    help="run the cutting-plane loop ({0,1/2}-cuts + Farkas) "
                         "instead of plain Farkas (for LP-feasible UNSAT like PHP)")
    args = ap.parse_args()
    if args.selftest:
        sys.exit(0 if selftest() else 1)
    if args.cnf:
        (refute_cg(args.cnf, verbose=True) if args.cg else refute_cnf(args.cnf))


if __name__ == "__main__":
    main()
