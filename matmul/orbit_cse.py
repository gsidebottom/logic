#!/usr/bin/env python3
"""Minimize CSE additions over a scheme's de Groote orbit.

The additive (CSE) cost is NOT a de-Groote invariant: within Stapleton's
class the stored DB representative plateaus at 62 while his
representative reaches 60. This hill-climbs the orbit with the CSE count
as objective: propose random (P,Q,R) sandwiches (+ S3 slot maps), score
with a cheap greedy-CSE evaluation, accept improvements (plus rare
sideways moves), and re-score incumbents at high effort.

Every accepted representative is re-verified mod-2; every reported count
is a replay-verified SLP.

Usage:
  python3 orbit_cse.py scheme.bits [--minutes 10] [--quick-models 2]
      [--quick-restarts 6] [--hi-models 12] [--hi-restarts 64]
      [--out best.bits] [--rng 1]
"""
import random
import sys
import time

from brent import verify_bits
from equiv import (apply_glw, bits_to_summands, rand_gl, s3_variants,
                   summands_to_bits)
from slp import best_cse

IDENT = 0b100010001  # 3x3 identity as 9-bit int
TRANSVECTIONS = [IDENT | (1 << (3 * i + j))
                 for i in range(3) for j in range(3) if i != j]


def cse_of(bits, nmodels, restarts, seed):
    r = best_cse(bits, nmodels, restarts, seed)
    return r[0] if r else 10 ** 9


def propose(cur, rng, p_local=0.85):
    """local move: one transvection on one side (dense neighborhood);
    else a full random jump (basin hop). Occasionally an S3 slot map."""
    if rng.random() < p_local:
        t = TRANSVECTIONS[rng.randrange(6)]
        side = rng.randrange(3)
        p = t if side == 0 else IDENT
        q = t if side == 1 else IDENT
        r = t if side == 2 else IDENT
        img = apply_glw(cur, p, q, r)
        if rng.random() < 0.15:
            img = s3_variants(img)[rng.randrange(6)]
        return img
    img = apply_glw(cur, rand_gl(rng), rand_gl(rng), rand_gl(rng))
    return s3_variants(img)[rng.randrange(6)]


def main():
    argv = sys.argv[1:]

    def opt(name, default, cast=int):
        if name in argv:
            i = argv.index(name)
            v = cast(argv[i + 1])
            del argv[i:i + 2]
            return v
        return default

    minutes = opt("--minutes", 10, float)
    qm = opt("--quick-models", 2)
    qr = opt("--quick-restarts", 6)
    hm = opt("--hi-models", 12)
    hr = opt("--hi-restarts", 64)
    out = opt("--out", None, str)
    seed = opt("--rng", 1)
    path = argv[0]

    s = open(path).read().split()[-1].strip()
    bits0 = [int(c) for c in s]
    assert verify_bits(bits0, 3, 3, 3, 23) == 0
    rng = random.Random(seed)

    cur = bits_to_summands(bits0)
    cur_score = cse_of(bits0, qm, qr, seed)
    best_bits = bits0
    best_hi = cse_of(bits0, hm, hr, seed)
    print(f"{path}: start quick={cur_score} hi={best_hi}", flush=True)

    t0 = time.time()
    n = acc = 0
    while time.time() - t0 < minutes * 60:
        n += 1
        img = propose(cur, rng)
        nb = summands_to_bits(img)
        sc = cse_of(nb, qm, qr, seed + n)
        # accept improvements always, equals often, +1 rarely (plateau walk)
        if sc < cur_score or (sc == cur_score and rng.random() < 0.5) \
                or (sc == cur_score + 1 and rng.random() < 0.03):
            acc += 1
            cur = img
            cur_score = min(cur_score, sc)
            if sc < best_hi:  # promising: re-score at high effort
                assert verify_bits(nb, 3, 3, 3, 23) == 0
                hi = cse_of(nb, hm, hr, seed + n)
                if hi < best_hi:
                    best_hi, best_bits = hi, nb
                    el = time.time() - t0
                    print(f"  [{el:6.1f}s n={n}] new best hi={hi} "
                          f"(quick {sc})", flush=True)
    print(f"{path}: done — best hi-effort CSE = {best_hi} "
          f"({n} proposals, {acc} accepted)", flush=True)
    if out:
        open(out, "w").write("".join(map(str, best_bits)) + "\n")
        print(f"wrote {out}")


if __name__ == "__main__":
    main()
