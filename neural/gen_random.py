#!/usr/bin/env python3
"""
Generate a synthetic random k-SAT corpus spanning the phase transition.

Random 3-SAT flips from mostly-SAT to mostly-UNSAT around clause/variable
ratio α ≈ 4.26.  Sampling α across that boundary yields a balanced SAT/
UNSAT mix — the corpus for the Phase-0 satisfiability-classification gate
(the standard "does the GNN learn SAT structure" test, à la NeuroSAT).

Writes plain DIMACS .cnf files + an index.jsonl (records:
{filename, family, path, nvars, nclauses}) consumable by build_dataset.py.

Usage:  gen_random.py --out <dir> --count N [--n-min 20 --n-max 80]
                      [--ratio-min 3.5 --ratio-max 5.5] [--k 3] [--seed 0]
"""
from __future__ import annotations

import argparse
import json
import os
import random


def gen_instance(rng: random.Random, n: int, m: int, k: int) -> list[list[int]]:
    clauses = []
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), k)
        clauses.append([v if rng.random() < 0.5 else -v for v in vs])
    return clauses


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--count", type=int, required=True)
    ap.add_argument("--n-min", type=int, default=20)
    ap.add_argument("--n-max", type=int, default=80)
    ap.add_argument("--ratio-min", type=float, default=3.5)
    ap.add_argument("--ratio-max", type=float, default=5.5)
    ap.add_argument("--k", type=int, default=3)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    rng = random.Random(args.seed)
    index = []
    for i in range(args.count):
        n = rng.randint(args.n_min, args.n_max)
        alpha = rng.uniform(args.ratio_min, args.ratio_max)
        m = max(1, round(alpha * n))
        clauses = gen_instance(rng, n, m, args.k)
        fname = f"rand_k{args.k}_n{n}_m{m}_{i:05d}.cnf"
        path = os.path.join(args.out, fname)
        with open(path, "w") as f:
            f.write(f"p cnf {n} {m}\n")
            for c in clauses:
                f.write(" ".join(map(str, c)) + " 0\n")
        index.append({"filename": fname, "family": f"random-{args.k}sat",
                      "path": path, "nvars": n, "nclauses": m})
    with open(os.path.join(args.out, "index.jsonl"), "w") as f:
        for r in index:
            f.write(json.dumps(r) + "\n")
    print(f"generated {len(index)} random {args.k}-SAT instances → {args.out}")
    print(f"  n ∈ [{args.n_min},{args.n_max}], α ∈ [{args.ratio_min},"
          f"{args.ratio_max}] (3-SAT threshold ≈ 4.26 → SAT/UNSAT mix)")


if __name__ == "__main__":
    main()
