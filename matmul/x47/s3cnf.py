#!/usr/bin/env python3
"""S3-quotient Brent system for <n,n,n> schemes over F2, as CNF.

Schemes invariant under the slot symmetry group S3 = <c, t> of the
matrix multiplication tensor, c: (U,V,W) -> (V, W^T, U^T) and
t: (U,V,W) -> (V^T, U^T, W^T)  (product m = <U_m,A><V_m,B>, C =
sum_m product_m W_m).  Product orbits have size 6, 3, 2 or 1:

  6-orbit, free A0, A1, A2:  (A0, A1, A2^T) (A1, A2, A0^T) (A2, A0, A1^T)
                             (A1^T, A0^T, A2) (A2^T, A1^T, A0) (A0^T, A2^T, A1)
  3-orbit, free A, symmetric S:   (A, A^T, S) (A^T, S, A^T) (S, A, A)
  2-orbit, free U:                (U, U, U^T) (U^T, U^T, U)
  1-orbit, symmetric S:           (S, S, S)

r = 6a + 3b + 2c + d.  The Brent equations (matmul/brent.py order) are
rewritten in the free entries (a symmetric matrix shares (i,j) and
(j,i)), reduced mod 2 and deduplicated; encoding as in cyccnf.py.

Usage: s3cnf.py n a b c d out.cnf [--xor]
       s3cnf.py decode n a b c d SOLVER_OUTPUT out.bits
       s3cnf.py map n a b c d out.map   (orbit file for `anf --orbit-file`:
           "v rep" per Brent variable, rep = first variable of its class)
"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))  # matmul/
from brent import brent_equations, verify_bits  # noqa: E402


def build(n, a, b, c, d):
    """Return (r, nvars, products) with products[m] = (U, V, W) as n x n
    lists of free-variable indices."""
    nv = 0

    def free():
        nonlocal nv
        m = [[nv + i * n + j for j in range(n)] for i in range(n)]
        nv += n * n
        return m

    def sym():
        nonlocal nv
        idx = {}
        for i in range(n):
            for j in range(i, n):
                idx[(i, j)] = nv
                nv += 1
        return [[idx[(min(i, j), max(i, j))] for j in range(n)] for i in range(n)]

    T = lambda M: [list(r) for r in zip(*M)]
    prods = []
    for _ in range(a):
        A0, A1, A2 = free(), free(), free()
        prods += [(A0, A1, T(A2)), (A1, A2, T(A0)), (A2, A0, T(A1)),
                  (T(A1), T(A0), A2), (T(A2), T(A1), A0), (T(A0), T(A2), A1)]
    for _ in range(b):
        A, S = free(), sym()
        prods += [(A, T(A), S), (T(A), S, T(A)), (S, A, A)]
    for _ in range(c):
        U = free()
        prods += [(U, U, T(U)), (T(U), T(U), U)]
    for _ in range(d):
        S = sym()
        prods += [(S, S, S)]
    return len(prods), nv, prods


def rep_map(n, a, b, c, d):
    r, nv, prods = build(n, a, b, c, d)
    nn = n * n
    rep = {}
    for m, (U, V, W) in enumerate(prods):
        for i in range(n):
            for j in range(n):
                rep[m * nn + i * n + j] = U[i][j]
                rep[r * nn + m * nn + i * n + j] = V[i][j]
                rep[2 * r * nn + m * nn + i * n + j] = W[i][j]
    return r, nv, rep


def reduced_equations(n, a, b, c, d):
    r, nv, rep = rep_map(n, a, b, c, d)
    seen, eqs = set(), []
    for mons, rhs in brent_equations(n, n, n, r):
        cnt = {}
        for mon in mons:
            q = tuple(sorted(set(rep[v] for v in mon)))
            cnt[q] = cnt.get(q, 0) ^ 1
        odd = frozenset(q for q, k in cnt.items() if k)
        if not odd:
            if rhs:
                return r, nv, None  # structurally UNSAT
            continue
        key = (odd, rhs)
        if key not in seen:
            seen.add(key)
            eqs.append((sorted(odd), rhs))
    return r, nv, eqs


def write_cnf(n, a, b, c, d, out, native):
    r, nfree, eqs = reduced_equations(n, a, b, c, d)
    if eqs is None:
        with open(out, "w") as f:
            f.write("c structurally UNSAT (an equation reduces to 0 = 1)\np cnf 1 2\n1 0\n-1 0\n")
        print(f"{out}: <{n},{n},{n}> r={r} S3 shape ({a},{b},{c},{d}): structurally UNSAT")
        return
    nv = nfree
    clauses, xors, monvar = [], [], {}

    def lit_of(mon):
        nonlocal nv
        if len(mon) == 1:
            return mon[0] + 1
        if mon not in monvar:
            nv += 1
            monvar[mon] = nv
            for x in mon:
                clauses.append([-nv, x + 1])
            clauses.append([nv] + [-(x + 1) for x in mon])
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
        f.write(f"c S3 quotient <{n},{n},{n}> r={r} shape (6x{a}, 3x{b}, 2x{c}, 1x{d}), "
                f"{len(eqs)} distinct equations, {nfree} scheme vars\n")
        f.write(f"p cnf {nv} {len(clauses) + len(xors)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
        for lits, rhs in xors:
            if not rhs:
                lits = [-lits[0]] + lits[1:]
            f.write("x" + " ".join(map(str, lits)) + " 0\n")
    print(f"{out}: <{n},{n},{n}> r={r} S3 shape ({a},{b},{c},{d}), {len(eqs)} equations, "
          f"{nfree} scheme vars, {nv} vars, {len(clauses) + len(xors)} clauses"
          f"{' (native XOR)' if native else ''}")


def decode(n, a, b, c, d, sol, out):
    val, sat = {}, None
    for ln in open(sol):
        if ln.startswith("s "):
            sat = "UNSATISFIABLE" not in ln and "SATISFIABLE" in ln
        if ln.startswith("v "):
            for tok in ln.split()[1:]:
                x = int(tok)
                if x:
                    val[abs(x)] = 1 if x > 0 else 0
    if not sat:
        raise SystemExit(f"{sol}: no satisfying model")
    r, _, rep = rep_map(n, a, b, c, d)
    bits = [val.get(rep[v] + 1, 0) for v in range(3 * r * n * n)]
    bad = verify_bits(bits, n, n, n, r)
    if bad:
        raise SystemExit(f"FAIL: {bad} Brent equations violated")
    open(out, "w").write("".join(map(str, bits)) + "\n")
    print(f"wrote {out}: <{n},{n},{n}> rank {r}, S3 shape ({a},{b},{c},{d}), all {(n * n) ** 3} Brent equations hold")


def write_map(n, a, b, c, d, out):
    r, nv, rep = rep_map(n, a, b, c, d)
    first = {}
    for v in sorted(rep):
        first.setdefault(rep[v], v)
    with open(out, "w") as f:
        for v in sorted(rep):
            f.write(f"{v} {first[rep[v]]}\n")
    print(f"wrote {out}: <{n},{n},{n}> r={r}, {len(rep)} vars -> {nv} classes")


if __name__ == "__main__":
    av = sys.argv
    if len(av) >= 8 and av[1] == "map":
        write_map(*map(int, av[2:7]), av[7])
    elif len(av) >= 9 and av[1] == "decode":
        decode(*map(int, av[2:7]), av[7], av[8])
    elif len(av) >= 7:
        write_cnf(*map(int, av[1:6]), av[6], "--xor" in av)
    else:
        raise SystemExit(__doc__)
