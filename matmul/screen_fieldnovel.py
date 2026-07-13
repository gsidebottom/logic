#!/usr/bin/env python3
"""Field-novelty screen over the F_p pursue7/storm pools.
For each pooled scheme, compute its de-Groote rank-type multiset
(sorted per-summand rank triples, ranks over the pool's own prime)
and test it against the 302 DB rank patterns via novelty.compatible.
Rank triples are field-equivalence invariants, and DB integer schemes
keep their Q-ranks over these large primes, so a multiset compatible
with NO DB pattern certifies a class new at the database level FOR
THAT FIELD (same standard as novelty.py, one-way).
Usage: python3 screen_fieldnovel.py pool.txt [...]
       (modulus inferred per path: 'p7b'/'bb' -> BabyBear,
        'm31' -> M31, else Goldilocks)
"""
import sys
from collections import Counter

from novelty import LEGEND, letters_of, compatible  # noqa: F401

GOLD = 0xFFFF_FFFF_0000_0001
BB = 2_013_265_921
M31 = 2_147_483_647


def modulus_of(path):
    if "p7b" in path or "bb" in path:
        return BB
    if "m31" in path:
        return M31
    return GOLD


def rank3(m, p):
    det = (m[0] * (m[4] * m[8] - m[5] * m[7])
           - m[1] * (m[3] * m[8] - m[5] * m[6])
           + m[2] * (m[3] * m[7] - m[4] * m[6])) % p
    if det:
        return 3
    for r1 in range(3):
        for r2 in range(r1 + 1, 3):
            for c1 in range(3):
                for c2 in range(c1 + 1, 3):
                    if (m[3 * r1 + c1] * m[3 * r2 + c2]
                            - m[3 * r1 + c2] * m[3 * r2 + c1]) % p:
                        return 2
    return 1 if any(x % p for x in m) else 0


def blocks(path):
    cur = []
    for ln in open(path):
        ln = ln.strip()
        if ln == "---":
            if len(cur) == 23:
                yield cur
            cur = []
            continue
        if not ln:
            continue
        parts = ln.split("|")
        if len(parts) != 3:
            continue
        cur.append([[int(x) for x in
                     seg.strip().strip("[]").split(",")] for seg in parts])
    if len(cur) == 23:
        yield cur


def main():
    patterns = [(p, letters_of(p))
                for p in open("db_rank_patterns.txt").read().split()]
    grand = {}
    for path in sys.argv[1:]:
        p = modulus_of(path)
        seen = Counter()
        for sch in blocks(path):
            key = tuple(sorted(
                tuple(sorted((rank3(a, p), rank3(b, p), rank3(c, p))))
                for a, b, c in sch))
            seen[key] += 1
        novel = {k: v for k, v in seen.items()
                 if not any(compatible(ls, Counter(k)) for _, ls in patterns)}
        print(f"{path} (p={'BB' if p==BB else 'M31' if p==M31 else 'G'}): "
              f"{sum(seen.values())} schemes, {len(seen)} distinct "
              f"multisets, {len(novel)} field-novel multisets "
              f"({sum(novel.values())} schemes)")
        for k in sorted(novel)[:6]:
            print(f"   novel: {dict(Counter(k))}  x{novel[k]}")
        for k, v in seen.items():
            grand.setdefault(k, [0, k in novel])
            grand[k][0] += v
    nov = [k for k, (c, isn) in grand.items() if isn]
    print(f"GRAND: {len(grand)} distinct multisets across all pools; "
          f"{len(nov)} field-novel vs the 302 DB patterns")


if __name__ == "__main__":
    main()
