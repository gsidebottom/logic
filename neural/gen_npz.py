#!/usr/bin/env python3
"""
Full-scale synthetic corpus: generate thousands of structured, guaranteed-SAT
instances and write the GNN .npz (literal-clause graph + planted-phase labels)
DIRECTLY — no solver needed, since each instance is built with a KNOWN planted
solution. Labels = the plant (a single satisfying assignment, like the
single-model harvest). Instant at scale.

Families (predictable phases from structure):
  planted-coloring : random graph k-colored by construction
  planted-ksat     : random σ, clauses kept satisfiable under σ
  php-sat          : pigeons ≤ holes, planted injective assignment

Usage:  gen_npz.py --out <dir> [--count N-per-family] [--seed S]
"""
from __future__ import annotations
import argparse, hashlib, json, os, random
import numpy as np
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sat_graph  # noqa: E402


def planted_coloring(rng, n, k, p):
    col = [rng.randrange(k) for _ in range(n)]
    def var(v, c): return v * k + c + 1
    nv = n * k; cl = []; plant = [False] * nv
    for v in range(n):
        cl.append([var(v, c) for c in range(k)])
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                cl.append([-var(v, c1), -var(v, c2)])
        plant[var(v, col[v]) - 1] = True
    for v in range(n):
        for w in range(v + 1, n):
            if col[v] != col[w] and rng.random() < p:
                for c in range(k):
                    cl.append([-var(v, c), -var(w, c)])
    return nv, cl, plant


def planted_ksat(rng, n, m, k):
    sigma = [rng.random() < 0.5 for _ in range(n)]
    cl = []
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), k)
        c = [v if rng.random() < 0.5 else -v for v in vs]
        if not any((l > 0) == sigma[abs(l) - 1] for l in c):
            i = rng.randrange(k); v = abs(c[i]); c[i] = v if sigma[v - 1] else -v
        cl.append(c)
    return n, cl, sigma


def php_sat(rng, pigeons, holes):
    def var(p, h): return p * holes + h + 1
    nv = pigeons * holes; cl = []; plant = [False] * nv
    perm = rng.sample(range(holes), pigeons)              # injective assignment
    for p in range(pigeons):
        cl.append([var(p, h) for h in range(holes)])
        for h1 in range(holes):
            for h2 in range(h1 + 1, holes):
                cl.append([-var(p, h1), -var(p, h2)])
        plant[var(p, perm[p]) - 1] = True
    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                cl.append([-var(p1, h), -var(p2, h)])
    return nv, cl, plant


def emit(out, name, family, nv, clauses, plant):
    g = sat_graph.build_graph(clauses, nv)
    h = hashlib.sha1(name.encode()).hexdigest()[:16]
    np.savez_compressed(
        os.path.join(out, f"{h}.npz"),
        edge_lit=g.edge_lit, edge_clause=g.edge_clause, flip=g.flip,
        n_vars=np.int64(nv), n_clauses=np.int64(len(clauses)),
        sat=np.int8(1),
        phase=np.fromiter((1 if plant[i] else 0 for i in range(nv)),
                          dtype=np.uint8, count=nv))
    return {"hash": h, "filename": name, "family": family, "sat": 1,
            "saved": True, "n_vars": nv, "n_clauses": len(clauses)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--count", type=int, default=700, help="instances per family")
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    rng = random.Random(args.seed)
    man = []
    for i in range(args.count):
        n = rng.randint(15, 70); k = rng.randint(3, 6); p = rng.uniform(0.15, 0.6)
        nv, cl, pl = planted_coloring(rng, n, k, p)
        man.append(emit(args.out, f"plcol_{n}_{k}_{i}", "synth-coloring", nv, cl, pl))
    for i in range(args.count):
        n = rng.randint(50, 450); m = max(1, round(rng.uniform(3.2, 4.2) * n))
        nv, cl, pl = planted_ksat(rng, n, m, 3)
        man.append(emit(args.out, f"plksat_{n}_{m}_{i}", "synth-ksat", nv, cl, pl))
    for i in range(args.count):
        pig = rng.randint(4, 13); hol = pig + rng.randint(1, 6)
        nv, cl, pl = php_sat(rng, pig, hol)
        man.append(emit(args.out, f"php_{pig}_{hol}_{i}", "synth-php", nv, cl, pl))
    # family-stratified split
    from collections import defaultdict
    by = defaultdict(list)
    for e in man:
        by[e["family"]].append(e)
    for fam, rows in by.items():
        rows.sort(key=lambda e: e["hash"])
        nt = max(1, round(len(rows) * 0.15))
        for j, e in enumerate(rows):
            e["split"] = "test" if j < nt else "train"
    with open(os.path.join(args.out, "manifest.jsonl"), "w") as f:
        for e in man:
            f.write(json.dumps(e) + "\n")
    print(f"emitted {len(man)} synthetic npz → {args.out} ({args.count}/family, no solver)")


if __name__ == "__main__":
    main()
