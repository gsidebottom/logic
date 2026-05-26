#!/usr/bin/env python3
"""
PHP-N-M proof generator using VeriPB `red` rules with cyclic
pigeon-permutation witnesses.

Polynomial-size proof: M-1 `red` steps, then a single `rup >= 1 ;`
empty-clause derivation.  Each red step asserts WLOG pigeon i is in
hole i (via cyclic permutation of pigeons i..N).  After M-1 such
steps, BCP from F + {x_{i,i}=1 for i=1..M-1} reaches contradiction.

Variable encoding (DIMACS): var(p, h) = (p-1)*M + h.

Usage:
    php_red_proof.py <N> <M> <out_dir>

Writes:
    <out_dir>/php_N_M.cnf   — DIMACS CNF
    <out_dir>/php_N_M.pbp   — VeriPB proof
"""
import sys, os

def php_proof(N, M):
    assert N > M, f"PHP-{N}-{M} only UNSAT when N > M"
    var = lambda p, h: (p - 1) * M + h

    # CNF clauses in the same order the matrix-method tests use:
    #   1..N: pigeon clauses (each pigeon must be in some hole)
    #   then mutex clauses, grouped by hole h, ordered by (p1, p2) lex
    cnf = []
    for p in range(1, N + 1):
        cnf.append([var(p, h) for h in range(1, M + 1)])
    for h in range(1, M + 1):
        for p1 in range(1, N + 1):
            for p2 in range(p1 + 1, N + 1):
                cnf.append([-var(p1, h), -var(p2, h)])

    # Proof:
    #   M-1 red steps; step i asserts x_{i,i} >= 1 with witness
    #   cycling pigeons i..N (i fixed first; i+1 takes i's old value, etc.)
    proof = [
        "pseudo-Boolean proof version 3.0",
        f"% PHP-{N}-{M} via cyclic-pigeon symmetry (red rules).",
        f"% Variables: x((p-1)*{M}+h) = pigeon p in hole h.",
        f"f {len(cnf)};",
        ""
    ]
    for i in range(1, M):
        # Cyclic permutation of pigeons {i, i+1, ..., N}: each pigeon
        # j maps to j+1, with the last (N) wrapping back to i.
        # Pigeons < i are fixed (not substituted), so previously-added
        # constraints x_{1,1} >= 1 ... x_{i-1,i-1} >= 1 are preserved.
        next_of = {j: (i if j == N else j + 1) for j in range(i, N + 1)}
        subs = []
        for j in range(i, N + 1):
            nj = next_of[j]
            if nj == j:
                continue
            for h in range(1, M + 1):
                v_from = var(j, h)
                v_to   = var(nj, h)
                subs.append(f"x{v_from} -> x{v_to}")
        proof.append(f"% Step {i}: WLOG pigeon {i} in hole {i}; "
                     f"witness = cyclic permutation of pigeons {i}..{N}.")
        proof.append(f"red 1 x{var(i, i)} >= 1 : {' '.join(subs)} ;")
        proof.append("")

    proof.append("% After M-1 red steps, pigeons M..N forced into 1 hole; "
                 "BCP finds contradiction.")
    proof.append("rup >= 1 ;")
    proof.append("output NONE;")
    proof.append("conclusion UNSAT : -1;")
    proof.append("end pseudo-Boolean proof;")
    return cnf, "\n".join(proof) + "\n"

def write_cnf(path, cnf, nvars):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(cnf)}\n")
        for c in cnf:
            f.write(" ".join(str(l) for l in c) + " 0\n")

def main():
    if len(sys.argv) != 4:
        print(__doc__); sys.exit(1)
    N = int(sys.argv[1]); M = int(sys.argv[2])
    out = sys.argv[3]
    os.makedirs(out, exist_ok=True)
    cnf, pbp = php_proof(N, M)
    nvars = N * M
    cnf_path = os.path.join(out, f"php_{N}_{M}.cnf")
    pbp_path = os.path.join(out, f"php_{N}_{M}.pbp")
    write_cnf(cnf_path, cnf, nvars)
    with open(pbp_path, "w") as f:
        f.write(pbp)
    print(f"wrote {cnf_path}: {nvars} vars, {len(cnf)} clauses")
    print(f"wrote {pbp_path}: {pbp.count(chr(10))} lines")

if __name__ == "__main__":
    main()
