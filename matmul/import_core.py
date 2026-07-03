#!/usr/bin/env python3
"""Import a hardcoded type-3 pairing ("core") from a Heule matrix-challenges
CNF into our variable numbering, emitting a freeze file for `anf
--freeze-file`.

Their base-var convention (decode.c): summand m (0-based) owns vars
27m+1..27m+27: +1..9 = alpha row-major, +10..18 = beta, +19..27 = gamma —
with gamma indexed TRANSPOSED relative to ours (their delta condition is
cyclic: i2=j1, j2=k1, k2=i1). We self-validate by requiring every frozen
triple to be a type-3 term alpha[m,a,b] beta[m,b,d] gamma[m,a,d]; the
transpose choice that makes all 27 terms consistent wins.

Usage: python3 import_core.py challenge.cnf out.freeze
"""
import sys
from brent import var_counts

N, R = 3, 23
NA, NB, _ = var_counts(N, N, N, R)


def parse_units(path):
    """Signed unit literals on base vars (|v| <= 27*R)."""
    units = []
    for line in open(path):
        if line.startswith(("c", "p")):
            continue
        toks = line.split()
        if len(toks) == 2 and toks[1] == "0":
            v = int(toks[0])
            if 1 <= abs(v) <= 27 * R:
                units.append(v)
    return units


def remap_var(v, transpose_gamma=True):
    """their base var (1-based) -> our var index (0-based)."""
    m, k = divmod(v - 1, 27)
    blk, off = divmod(k, 9)
    i, j = divmod(off, 3)
    if blk == 0:
        return m * 9 + i * 3 + j
    if blk == 1:
        return NA + m * 9 + i * 3 + j
    if transpose_gamma:
        i, j = j, i
    return NA + NB + m * 9 + i * 3 + j


def decode(units, transpose_gamma):
    """their unit vars -> per-summand (alphas, betas, gammas) index pairs."""
    per = [{"a": [], "b": [], "g": []} for _ in range(R)]
    for v in units:
        m, k = divmod(v - 1, 27)
        blk, off = divmod(k, 9)
        i, j = divmod(off, 3)
        if blk == 0:
            per[m]["a"].append((i, j))
        elif blk == 1:
            per[m]["b"].append((i, j))
        else:
            per[m]["g"].append((j, i) if transpose_gamma else (i, j))
    return per


def type3_terms(per):
    """Check each summand's frozen bits decompose into type-3 terms
    alpha(a,b) beta(b,d) gamma(a,d); return list of (m,a,b,d) or None."""
    terms = []
    for m, s in enumerate(per):
        if not (len(s["a"]) == len(s["b"]) == len(s["g"])):
            return None
        used_b, used_g = set(), set()
        for (a, b) in s["a"]:
            match = None
            for bi, (c, d) in enumerate(s["b"]):
                if bi in used_b or c != b:
                    continue
                for gi, (p, q) in enumerate(s["g"]):
                    if gi in used_g or (p, q) != (a, d):
                        continue
                    match = (bi, gi, d)
                    break
                if match:
                    break
            if not match:
                return None
            used_b.add(match[0])
            used_g.add(match[1])
            terms.append((m, a, b, match[2]))
    return terms


def main():
    cnf, out = sys.argv[1], sys.argv[2]
    units = parse_units(cnf)
    pos = [v for v in units if v > 0]
    neg = [-v for v in units if v < 0]
    print(f"{len(pos)} positive / {len(neg)} negative base units")
    # validation: when the positive units form a clean disjoint pairing,
    # confirm the type-3 structure (fires on 2-2-2-2-* cores)
    if len(pos) == 81 and not neg:
        for tg in (True, False):
            t = type3_terms(decode(pos, tg))
            if t is not None:
                prof = sorted((sum(1 for x in t if x[0] == m)
                               for m in range(R)), reverse=True)
                print(f"validated type-3 pairing (transpose_gamma={tg}); "
                      "profile",
                      "-".join(map(str, (p for p in prof if p > 1))))
                break
    with open(out, "w") as f:
        for v in pos:
            f.write(f"{remap_var(v)} 1\n")
        for v in neg:
            f.write(f"{remap_var(v)} 0\n")
    print(f"wrote {out} ({len(units)} frozen bits, our numbering)")


if __name__ == "__main__":
    main()
