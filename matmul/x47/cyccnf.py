#!/usr/bin/env python3
"""Cyclic-quotient Brent system for <n,n,n> schemes over F2, as CNF.

A scheme invariant under the cyclic symmetry (U, V, W) -> (V, W^T, U^T)
of the matrix multiplication tensor (product m = <U_m, A><V_m, B>,
C = sum_m product_m W_m) has products in 3-orbits and fixed points.
With r = 3a + b (a orbits, then b fixed products), product m keeps its
A-factor U_m as free variables, and
    V_m = U_succ(m),   W_m = U_pred(m)^T
(succ/pred rotate within an orbit; a fixed product is its own succ and
pred, i.e. (U, U, U^T)).  Only r*n^2 variables remain.  The Brent
equations (matmul/brent.py order) are rewritten in those variables,
reduced mod 2 (idempotent monomials, cancelling pairs), and duplicates
removed -- equations in one symmetry orbit become identical.

Encoding: one Tseitin AND per distinct monomial; each equation an XOR
of monomial literals, either as CryptoMiniSat native XOR clauses
(--xor) or as a Tseitin XOR ladder (kissat/cadical).  CNF variable
v + 1 is A-factor bit v (product m, entry (i, j) at m*n*n + i*n + j).

Usage: cyccnf.py n a b out.cnf [--xor]
"""
import sys

import pathlib  # noqa: E402
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))  # matmul/
from brent import brent_equations  # noqa: E402


def orbit_maps(n, a, b):
    r = 3 * a + b
    succ, pred = list(range(r)), list(range(r))
    for i in range(a):
        for j in range(3):
            succ[3 * i + j] = 3 * i + (j + 1) % 3
            pred[3 * i + j] = 3 * i + (j + 2) % 3
    return r, succ, pred


def rep_map(n, a, b):
    """Brent variable index -> A-factor variable index."""
    r, succ, pred = orbit_maps(n, a, b)
    nn = n * n
    rep = {}
    for m in range(r):
        for i in range(n):
            for j in range(n):
                rep[m * nn + i * n + j] = m * nn + i * n + j                       # alpha
                rep[r * nn + m * nn + i * n + j] = succ[m] * nn + i * n + j        # beta
                rep[2 * r * nn + m * nn + i * n + j] = pred[m] * nn + j * n + i    # gamma^T
    return r, rep


def reduced_equations(n, a, b):
    r, rep = rep_map(n, a, b)
    seen, eqs = set(), []
    for mons, rhs in brent_equations(n, n, n, r):
        cnt = {}
        for mon in mons:
            q = tuple(sorted(set(rep[v] for v in mon)))
            cnt[q] = cnt.get(q, 0) ^ 1
        odd = frozenset(q for q, c in cnt.items() if c)
        if not odd:
            if rhs:
                raise SystemExit(f"structurally UNSAT: an equation reduces to 0 = 1 (n={n}, a={a}, b={b})")
            continue
        key = (odd, rhs)
        if key not in seen:
            seen.add(key)
            eqs.append((sorted(odd), rhs))
    return r, eqs


def main(argv):
    if len(argv) < 5:
        raise SystemExit(__doc__)
    n, a, b, out = int(argv[1]), int(argv[2]), int(argv[3]), argv[4]
    native = "--xor" in argv
    r, eqs = reduced_equations(n, a, b)
    nv = r * n * n
    clauses, xors = [], []
    monvar = {}

    def lit_of(mon):
        nonlocal nv
        if len(mon) == 1:
            return mon[0] + 1
        if mon not in monvar:
            nv += 1
            t = nv
            monvar[mon] = t
            for x in mon:
                clauses.append([-t, x + 1])
            clauses.append([t] + [-(x + 1) for x in mon])
        return monvar[mon]

    for mons, rhs in eqs:
        lits = [lit_of(tuple(m)) for m in mons]
        if native:
            xors.append((lits, rhs))
            continue
        cur = lits[0]
        for l in lits[1:]:
            nv += 1
            o = nv
            clauses += [[-o, cur, l], [-o, -cur, -l], [o, -cur, l], [o, cur, -l]]
            cur = o
        clauses.append([cur] if rhs else [-cur])

    with open(out, "w") as f:
        f.write(f"c cyclic quotient <{n},{n},{n}> r={r} ({a} orbits + {b} fixed), "
                f"{len(eqs)} distinct equations, {r * n * n} scheme vars\n")
        f.write(f"p cnf {nv} {len(clauses) + len(xors)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
        for lits, rhs in xors:
            if not rhs:  # CMS "x" clause asserts XOR = 1; flip one literal for 0
                lits = [-lits[0]] + lits[1:]
            f.write("x" + " ".join(map(str, lits)) + " 0\n")
    print(f"{out}: <{n},{n},{n}> r={r} ({a}x3 + {b}), {len(eqs)} equations, "
          f"{len(monvar)} monomial auxes, {nv} vars, {len(clauses) + len(xors)} clauses"
          f"{' (native XOR)' if native else ''}")


if __name__ == "__main__":
    main(sys.argv)
