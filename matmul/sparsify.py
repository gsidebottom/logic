#!/usr/bin/env python3
"""Support (naive-addition) minimization over a scheme's de Groote orbit.

The symmetry group preserves validity and equivalence class but changes
the coefficient support, so the sparsest representative of a scheme's
orbit has the fewest naive additions (adds = support - 55 for 3x3x23).
Hill-climb: apply random (P,Q,R) in GL(3,2)^3 (and the 6 S3 slot maps),
keep images with lower support; restart from the incumbent. HKS did the
same with random group elements ("simplify" stage, ~20% of schemes
improved).

Every improved representative is re-verified against the Brent equations
before acceptance.

Usage: python3 sparsify.py scheme.bits [...] [--iters 4000] [--out DIR]
"""
import os
import random
import sys

from brent import verify_bits
from equiv import (apply_glw, bits_to_summands, rand_gl, s3_variants,
                   summands_to_bits)


def support(summands):
    return sum(bin(a).count("1") + bin(b).count("1") + bin(c).count("1")
               for a, b, c in summands)


def sparsify(summands, rng, iters=4000):
    best = min((s3_variants(summands)), key=support)
    bsup = support(best)
    stale = 0
    while stale < iters:
        p, q, r = rand_gl(rng), rand_gl(rng), rand_gl(rng)
        img = apply_glw(best, p, q, r)
        cand = min(s3_variants(img), key=support)
        csup = support(cand)
        if csup < bsup:
            best, bsup = cand, csup
            stale = 0
        else:
            stale += 1
    return best, bsup


def main():
    argv = sys.argv[1:]
    iters = 4000
    outdir = None
    if "--iters" in argv:
        i = argv.index("--iters")
        iters = int(argv[i + 1])
        argv = argv[:i] + argv[i + 2:]
    if "--out" in argv:
        i = argv.index("--out")
        outdir = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
        os.makedirs(outdir, exist_ok=True)
    rng = random.Random(1)
    for path in argv:
        s = open(path).read().split()[-1].strip()
        bits = [int(c) for c in s]
        assert verify_bits(bits, 3, 3, 3, 23) == 0
        summ = bits_to_summands(bits)
        s0 = support(summ)
        best, bsup = sparsify(summ, rng, iters)
        nb = summands_to_bits(best)
        assert verify_bits(nb, 3, 3, 3, 23) == 0, "orbit image must verify"
        name = os.path.basename(path)
        print(f"{name}: support {s0} -> {bsup} "
              f"(naive adds {s0 - 55} -> {bsup - 55})", flush=True)
        if outdir:
            open(f"{outdir}/{name}", "w").write(
                "".join(map(str, nb)) + "\n")


if __name__ == "__main__":
    main()
