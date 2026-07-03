#!/usr/bin/env python3
"""Canonicalize schemes by summand sorting (the HKS "distinct after
sorting summands" test) and dedupe.

Reads `b <bitstring>` lines (anf solver output) or raw bitstrings, one per
line, from files or stdin. Each scheme is verified against the Brent
equations before counting. The canonical key sorts the r summands by their
(alpha, beta, gamma) bit-block tuple; schemes equal after sorting are the
same scheme up to product reordering (NOT full de Groote equivalence —
sandwiching/cyclic images still count as distinct here, as in the paper's
neighborhood statistics).

Usage: python3 canon.py n1 n2 n3 r [file ...] [--emit PREFIX]
  --emit PREFIX   write each distinct scheme (first representative, original
                  bit order) to PREFIX-<i>.bits
"""
import sys
from brent import var_counts, verify_bits


def canon_key(bits, n1, n2, n3, r):
    na, nb, _ = var_counts(n1, n2, n3, r)
    sa, sb, sg = n1 * n2, n2 * n3, n1 * n3
    summands = []
    for m in range(r):
        a = tuple(bits[m * sa:(m + 1) * sa])
        b = tuple(bits[na + m * sb: na + (m + 1) * sb])
        g = tuple(bits[na + nb + m * sg: na + nb + (m + 1) * sg])
        summands.append((a, b, g))
    return tuple(sorted(summands))


def main():
    n1, n2, n3, r = map(int, sys.argv[1:5])
    nv = sum(var_counts(n1, n2, n3, r))
    lines = []
    files = sys.argv[5:]
    emit = None
    if "--emit" in files:
        i = files.index("--emit")
        emit = files[i + 1]
        files = files[:i] + files[i + 2:]
    for src in files if files else [None]:
        f = open(src) if src else sys.stdin
        for line in f:
            line = line.strip()
            if line.startswith("b "):
                line = line[2:]
            if len(line) == nv and set(line) <= {"0", "1"}:
                lines.append(line)
    seen = {}
    rep = {}
    bad = 0
    for s in lines:
        bits = [int(c) for c in s]
        if verify_bits(bits, n1, n2, n3, r) != 0:
            bad += 1
            continue
        k = canon_key(bits, n1, n2, n3, r)
        seen.setdefault(k, []).append(sum(bits))
        rep.setdefault(k, s)
    print(f"{len(lines)} schemes read, {bad} INVALID, "
          f"{len(seen)} distinct after summand sorting")
    for i, (k, sups) in enumerate(seen.items()):
        print(f"  scheme {i}: x{len(sups)}, support {sups[0]}")
        if emit:
            with open(f"{emit}-{i}.bits", "w") as f:
                f.write(rep[k] + "\n")
    if emit:
        print(f"wrote {len(seen)} files to {emit}-*.bits")


if __name__ == "__main__":
    main()
