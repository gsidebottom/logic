#!/usr/bin/env python3
"""Rank-pattern novelty test against the Kauers/Heule/Seidl database.

The DB organizes its 17,372 schemes into 302 directories named by a
letter-coded multiset of per-summand rank types (legend fitted from our 20
sampled dir<->scheme pairs, constraint-solved in-session; letters refine
sorted rank triples by slot position, so we compare at the COARSE
sorted-triple level, which is sound for an absence test):

    a=(1,1,1)  b,d,j=(1,1,2)  c,g,s=(1,1,3)  e,k,m=(1,2,2)
    f(,+unseen)=(1,2,3)  n=(2,2,2)  w=(2,2,3)

A scheme whose sorted-rank-triple multiset is COMPATIBLE with no DB
pattern cannot be equivalent to any DB scheme (rank triples are de-Groote
invariants) => certified new at the database level. Patterns containing
letters outside the fitted legend are treated as wildcards (any type),
which only WEAKENS our claim - never falsely certifies.

Usage: python3 novelty.py db_rank_patterns.txt scheme.bits [...]
"""
import re
import sys
from collections import Counter

from equiv import load_schemes, mat_rank

LEGEND = {
    "a": (1, 1, 1),
    "b": (1, 1, 2), "d": (1, 1, 2), "j": (1, 1, 2),
    "c": (1, 1, 3), "g": (1, 1, 3), "s": (1, 1, 3),
    "e": (1, 2, 2), "k": (1, 2, 2), "m": (1, 2, 2),
    "f": (1, 2, 3),
    "n": (2, 2, 2),
    "w": (2, 2, 3),
}
ALL_TYPES = [(1, 1, 1), (1, 1, 2), (1, 1, 3), (1, 2, 2), (1, 2, 3),
             (2, 2, 2), (2, 2, 3), (1, 3, 3), (2, 3, 3), (3, 3, 3)]


def letters_of(pat):
    out = Counter()
    for cnt, let in re.findall(r"([0-9]*)([a-z])", pat):
        out[let] += int(cnt) if cnt else 1
    return out


def scheme_types(summands):
    return Counter(
        tuple(sorted((mat_rank(a), mat_rank(b), mat_rank(c))))
        for (a, b, c) in summands)


def compatible(pattern_letters, types):
    """could `pattern_letters` coarsen to the multiset `types`?
    Known letters must fit inside their type's count; wildcard letters may
    cover any remaining counts."""
    remaining = Counter(types)
    wild = 0
    for let, c in pattern_letters.items():
        t = LEGEND.get(let)
        if t is None:
            wild += c
        else:
            if remaining[t] < c:
                return False
            remaining[t] -= c
    return sum(remaining.values()) == wild


def main():
    pat_file, files = sys.argv[1], sys.argv[2:]
    patterns = [(p, letters_of(p))
                for p in open(pat_file).read().split()]
    unknown = sorted({l for _, ls in patterns for l in ls} - set(LEGEND))
    nwild = sum(1 for _, ls in patterns
                if any(l not in LEGEND for l in ls))
    print(f"{len(patterns)} DB patterns; unknown letters {unknown} "
          f"appear in {nwild} patterns (treated as wildcards)")
    new = existing = 0
    for name, summ in load_schemes(files):
        types = scheme_types(summ)
        hits = [p for p, ls in patterns if compatible(ls, types)]
        if not hits:
            new += 1
            print(f"  CERTIFIED-NEW rank pattern: {name.split('/')[-1]} "
                  f"{dict(sorted(types.items()))}")
        else:
            existing += 1
    print(f"{new} certified-new at DB level / {existing} match an existing "
          f"DB rank pattern (novelty undecided without per-dir check)")


if __name__ == "__main__":
    main()
