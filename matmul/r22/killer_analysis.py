#!/usr/bin/env python3
"""Analysis of the killer-fold dump (matmul/r22/killers.txt, produced by
schemesearch3 --killer-dump): the adversary's koszul-dropping folds at the
211 first-product orbit roots.

FINDINGS (2026-08-31):
  * pivot is always coordinate 8 = cell (2,2); every root/side has killers;
    every killer drops koszul 14 -> exactly 13, never lower.
  * THE RANK LAW: view the folding covector phi = e_(2,2) + lambda as a
    3x3 F2 matrix. Then across all 633 (root, side) pairs:
      - rank(phi) = 1  =>  killer          (633/633, no exceptions)
      - rank(phi) = 3  =>  NOT a killer    (633/633, no exceptions)
      - rank(phi) = 2  =>  killer only at 38 exceptional pairs
        (30 roots, skewed toward low-rank-factor reps; 210 extra folds)
  * rank-1 covectors with the pivot cell set are the 4x4 = 16 rectangle
    indicators through (2,2) — exactly the observed 16 killers/pair.
  * Interpretation: the dangerous adversary moves are PRODUCT-SHAPED
    (rank-1, aligned with the tensor's own rank-one structure) — the same
    objects the subgame's rank-profile splits singled out.
  * CONJECTURE (the case-split lemma): folding by a rank-3 covector
    preserves koszul >= 14 on these residuals. Proven, it removes
    ~168/256 evals per probe sweep; with the rank-2 boundary handled,
    240/256 — repricing the t=16 rung from >= 1.5 core-years to days.
"""
import re
from collections import Counter, defaultdict


def mat_rank3(bits9):
    rows = [bits9 & 7, bits9 >> 3 & 7, bits9 >> 6 & 7]
    rk = 0
    for c in (2, 1, 0):
        piv = next((i for i in range(rk, 3) if rows[i] >> c & 1), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(3):
            if i != rk and rows[i] >> c & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rk


def main():
    rows = []
    for line in open("matmul/r22/killers.txt"):
        m = re.match(
            r"root (\d+) rep (\d+),(\d+),(\d+) own (\d+) side (\d+) pivot (\d+) lam (\d+) koszul (\d+)",
            line,
        )
        if m:
            rows.append(tuple(int(x) for x in m.groups()))
    per_rs = defaultdict(set)
    for r in rows:
        per_rs[(r[0], r[5])].add(r[7])
    rank1 = {l for l in range(256) if mat_rank3((1 << 8) | l) == 1}
    exact = sum(1 for v in per_rs.values() if v == rank1)
    superset = sum(1 for v in per_rs.values() if rank1 < v)
    viol = sum(1 for v in per_rs.values() if not rank1 <= v)
    extras = Counter(
        mat_rank3((1 << 8) | l)
        for v in per_rs.values()
        for l in v - rank1
    )
    print(f"killers: {len(rows)}; pairs: {len(per_rs)}")
    print(f"exact rank-1 law: {exact}; supersets: {superset}; violations: {viol}")
    print(f"extra-killer phi ranks: {dict(extras)}")


if __name__ == "__main__":
    main()
