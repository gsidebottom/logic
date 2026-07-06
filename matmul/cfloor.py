#!/usr/bin/env python3
"""DB-wide GF(2) output-side floors: the closing move for 54.

A fat-sides 54 (GF(2) input sides >= 28) needs a GF(2)-exact output
side <= 26, i.e. an XOR cover of the C-role masks costing <= 12 (the
transposition constant is r - 9 = 14).  The C-role masks of any
representative of a class are an (X (x) Y)-sandwich image (X, Y in
GL(3,2), plus the factor swap) of one of the class's THREE tensor
slots, with product permutations irrelevant.

Counting kills almost everything: X (x) Y is bijective on masks, so
d = #distinct nonzero masks of a slot is orbit-invariant, and any
chain containing d distinct values from 9 inputs uses >= d - 9 XORs.
  d = 23  ->  cover >= 14  ->  C_GF2 >= 28  (fat total >= 56)
  d = 22  ->  cover >= 13  ->  C_GF2 >= 27  (fat total >= 55: no 54)
  d <= 21 ->  counting insufficient -> sweep the 2 x 168^2 orbit
              images: prefilter nt >= 13, IDDFS the rest for
              cover <= 13 (55-capable) / <= 12 (54-capable).

Usage:
  cfloor.py census [LIST ...]      # stage 1: d per slot, histogram
  cfloor.py sweep NAME [NAME ...]  # stage 2 for named classes
  cfloor.py sweep-all              # stage 2 for every d<=22 slot
  (LIST default: dbcache/all_schemes.txt; extra .bits files may be
   appended as paths.)
"""
import os
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from gf2min import gf2_min_cover

HERE = __file__.rsplit("/", 1)[0]
R = 23


def slot_masks(bits):
    """the three 23-mask families (alpha, beta, gamma), 9-bit each."""
    out = []
    for base in (0, 207, 414):
        fam = []
        for m in range(R):
            w = 0
            for k in range(9):
                if bits[base + 9 * m + k]:
                    w |= 1 << k
            fam.append(w)
        out.append(fam)
    return out


def iter_schemes(sources):
    for src in sources:
        if src.endswith(".bits"):
            name = os.path.basename(src)[:-5]
            bits = [int(c) for c in open(src).read().split()[-1].strip()]
            yield name, bits
        else:
            for ln in open(src):
                name, s = ln.split()
                yield name, [int(c) for c in s]


# ---- stage 1: invariant census ----
def census(sources):
    from collections import Counter
    hist = Counter()
    cand54, cand55 = [], []
    zeros = 0
    n = 0
    for name, bits in iter_schemes(sources):
        n += 1
        ds = []
        for fam in slot_masks(bits):
            nz = [w for w in fam if w]
            zeros += len(fam) - len(nz)
            ds.append(len(set(nz)))
        dmin = min(ds)
        hist[dmin] += 1
        if dmin <= 21:
            cand54.append((name, ds))
        elif dmin == 22:
            cand55.append((name, ds))
    print(f"census over {n} schemes; zero-masks seen: {zeros}")
    print("min-slot distinct-mask histogram (d):")
    for d in sorted(hist):
        print(f"  d={d}: {hist[d]} classes")
    print(f"54-relevant (some slot d<=21): {len(cand54)}")
    for name, ds in cand54:
        print(f"  CAND54 {name} slots d={ds}")
    print(f"55-relevant only (min slot d=22): {len(cand55)}")
    with open(f"{HERE}/dbcache/cfloor_cands.txt", "w") as f:
        for name, ds in cand54 + cand55:
            f.write(f"{name} {ds[0]} {ds[1]} {ds[2]}\n")
    print(f"candidates written to dbcache/cfloor_cands.txt")


# ---- stage 2: orbit sweep for one slot ----
#
# Cover cost is invariant under any PERMUTATION of the 9 OUTPUT
# coordinates (units map to units, a chain transforms verbatim).  A
# permutation sigma_A (x) sigma_B of the output pair (a, b) permutes
# the BITS of every image row, i.e. replaces X by X.P (a COLUMN
# permutation, right coset X.S3), so (X, Y) only matters up to
# independent right-S3 cosets: 28 x 28 = 784 images instead of 168^2.
# (Row permutations P.X are NOT free: they permute the input masks'
# coordinates and change the image set — validated empirically.)
# The factor swap S obeys {S(X(x)Y)m} = {(Y(x)X)m' : m' in swap(fam)},
# and S is an output permutation, so sweeping the plain family over
# all (X, Y) already covers the swapped family; it is dropped.
POPC = [bin(i).count("1") for i in range(512)]


def gl32():
    """all 168 invertible 3x3 GF(2) matrices, as row-triples."""
    from itertools import product
    mats = []
    for rows in product(range(1, 8), repeat=3):
        r1, r2, r3 = rows
        if r1 ^ r2 and r1 ^ r3 and r2 ^ r3 and r1 ^ r2 ^ r3:
            mats.append(rows)
    assert len(mats) == 168
    return mats


def s3_coset_reps():
    """28 right-coset representatives X.S3 (S3 = column permutations)
    in GL(3,2)."""
    from itertools import permutations
    G = gl32()
    perms = list(permutations(range(3)))
    seen, reps = set(), []
    for X in G:
        if X in seen:
            continue
        reps.append(X)
        for p in perms:
            seen.add(tuple(sum(((r >> j) & 1) << p[j] for j in range(3))
                           for r in X))
    assert len(reps) == 28, len(reps)
    return reps


# tensor(xrow, yrow) -> 9-bit mask over index 3*a + b
TENSOR = [[sum(1 << (3 * a + b)
               for a in range(3) if (x >> a) & 1
               for b in range(3) if (y >> b) & 1)
           for y in range(8)] for x in range(8)]


def sweep_slot(fam):
    """min XOR cover over the 784 canonical (X (x) Y) images of the
    mask family; IDDFS only where the nt prefilter allows cover <= 13.
    Returns (best_cover<=13 or None, witness_count_at_13, hit12)."""
    reps = s3_coset_reps()
    bitlists = [[i for i in range(9) if (w >> i) & 1] for w in fam if w]
    best, n13, hit12 = None, 0, None
    for X in reps:
        for Y in reps:
            b = [TENSOR[X[p]][Y[q]] for p in range(3) for q in range(3)]
            img = []
            for bl in bitlists:
                v = 0
                for i in bl:
                    v ^= b[i]
                img.append(v)
            nt = len({w for w in img if POPC[w] >= 2})
            if nt > 13:
                continue
            res = gf2_min_cover(img, 9, max_slack=13 - nt,
                                node_cap=5_000_000)
            if res["status"] != "exact" or res["adds"] > 13:
                continue
            c = res["adds"]
            if best is None or c < best:
                best = c
            if c == 13:
                n13 += 1
            if c <= 12:
                hit12 = (X, Y, c)
    return best, n13, hit12


def sweep(names, sources):
    wanted = set(names)
    seen = set()
    for name, bits in iter_schemes(sources):
        if name not in wanted:
            continue
        seen.add(name)
        for si, fam in enumerate(slot_masks(bits)):
            d = len({w for w in fam if w})
            if d > 22:
                continue          # counting: cover >= 14 on every image
            best, n13, hit12 = sweep_slot(fam)
            tag = f"{name} slot{si} d={d}"
            if hit12:
                print(f"ALARM54 {tag}: cover {hit12[2]} -> C_GF2 <= "
                      f"{hit12[2] + 14} at X={hit12[0]} Y={hit12[1]}",
                      flush=True)
            elif best == 13:
                print(f"FAT55 {tag}: orbit-min cover 13 (C_GF2 = 27 "
                      f"reachable, {n13} canonical images)", flush=True)
            else:
                print(f"OK {tag}: no orbit image with cover <= 13 "
                      f"(C_GF2 >= 28 on every representative)",
                      flush=True)
    for name in wanted - seen:
        print(f"WARNING not found in sources: {name}", flush=True)


def main():
    args = sys.argv[1:]
    default_src = f"{HERE}/dbcache/all_schemes.txt"
    if args[:1] == ["census"]:
        srcs = args[1:] or [default_src]
        census(srcs)
    elif args[:1] == ["sweep"]:
        sweep(args[1:], [default_src])
    elif args[:1] == ["sweep-list"]:
        names = [ln.split()[0] for ln in open(args[1])]
        sweep(names, [default_src])
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
