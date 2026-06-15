#!/usr/bin/env python3
"""
Generate structured, guaranteed-SAT instances with PREDICTABLE phase structure,
to scale the phase-prediction corpus (§4b data effort).  Unlike random k-SAT
(phases unpredictable), these have a planted solution whose phases correlate
with local graph structure — what the GNN can learn.

Families:
  planted-coloring : random graph k-colored by construction (edges only between
                     differently-colored vertices) → the planted one-hot
                     coloring is a model; strong per-variable phase structure.
  planted-ksat     : random assignment σ, clauses each kept satisfiable under σ
                     (flip a literal if all-false) → σ is a model; backbone-ish.

Writes plain DIMACS .cnf + an index.jsonl consumable by build_dataset.py.

Usage:  gen_structured.py --out <dir> [--count-per-family N] [--seed S]
"""
from __future__ import annotations
import argparse, json, os, random


def planted_coloring(rng, n, k, p):
    """n vertices, k colors; var(v,c) = v*k + c + 1 (1-based)."""
    col = [rng.randrange(k) for _ in range(n)]
    def var(v, c): return v * k + c + 1
    clauses = []
    for v in range(n):                              # each vertex gets >=1 color
        clauses.append([var(v, c) for c in range(k)])
        for c1 in range(k):                         # at most one color
            for c2 in range(c1 + 1, k):
                clauses.append([-var(v, c1), -var(v, c2)])
    for v in range(n):                              # edges only between diff colors
        for w in range(v + 1, n):
            if col[v] != col[w] and rng.random() < p:
                for c in range(k):
                    clauses.append([-var(v, c), -var(w, c)])
    return n * k, clauses


def planted_ksat(rng, n, m, k):
    sigma = [rng.random() < 0.5 for _ in range(n)]   # planted assignment
    clauses = []
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), k)
        cl = [v if rng.random() < 0.5 else -v for v in vs]
        if not any((lit > 0) == sigma[abs(lit) - 1] for lit in cl):
            i = rng.randrange(k)                      # force >=1 true under sigma
            v = abs(cl[i]); cl[i] = v if sigma[v - 1] else -v
        clauses.append(cl)
    return n, clauses


def write_cnf(path, nvars, clauses):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--count-per-family", type=int, default=300)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    rng = random.Random(args.seed)
    index = []
    for i in range(args.count_per_family):
        n = rng.randint(15, 90); k = rng.randint(3, 6); p = rng.uniform(0.15, 0.55)
        nv, cl = planted_coloring(rng, n, k, p)
        fn = f"plcol_n{n}_k{k}_{i:05d}.cnf"
        write_cnf(os.path.join(args.out, fn), nv, cl)
        index.append({"filename": fn, "path": os.path.join(args.out, fn),
                      "family": "planted-coloring", "nvars": nv, "nclauses": len(cl)})
    for i in range(args.count_per_family):
        n = rng.randint(60, 600); ratio = rng.uniform(3.2, 4.2)
        m = max(1, round(ratio * n))
        nv, cl = planted_ksat(rng, n, m, 3)
        fn = f"plksat_n{n}_m{m}_{i:05d}.cnf"
        write_cnf(os.path.join(args.out, fn), nv, cl)
        index.append({"filename": fn, "path": os.path.join(args.out, fn),
                      "family": "planted-ksat", "nvars": nv, "nclauses": len(cl)})
    with open(os.path.join(args.out, "index.jsonl"), "w") as f:
        for r in index:
            f.write(json.dumps(r) + "\n")
    print(f"generated {len(index)} structured instances → {args.out} "
          f"({args.count_per_family}/family)")


if __name__ == "__main__":
    main()
