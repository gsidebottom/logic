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
from scipy.optimize import linprog

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
    args = ap.parse_args()
    if args.selftest:
        sys.exit(0 if selftest() else 1)
    if args.cnf:
        refute_cnf(args.cnf)


if __name__ == "__main__":
    main()
