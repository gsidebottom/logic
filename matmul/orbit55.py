#!/usr/bin/env python3
"""The 55-hunt: minimize (exact A side + exact B side + heuristic C)
over a scheme's de Groote orbit.

Within one class, representatives with optimal input sides (13+13 on
Sun's rep) and representatives with C = 28 (cr58-cn120) coexist; a
single representative with both gives <= 55 additions — an outright
record.  This walks the orbit with the exact side-minimizer
(sidemin.min_side) scoring A and B, and restart-greedy CSE scoring C.

Two-tier scoring like orbit_cse.py: cheap quick score for the walk,
high-effort re-score for incumbents.  Every accepted representative is
re-verified mod-2; sign models are Z-verified inside scheme scoring;
side chains replay-verified at hi-effort.

Usage:
  python3 orbit55.py scheme.bits [--minutes 30] [--quick-models 2]
      [--quick-crestarts 8] [--hi-models 12] [--hi-crestarts 300]
      [--out best.bits] [--rng 1] [--jackpot 55]
"""
import random
import sys
import time

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from brent import verify_bits
from equiv import (apply_glw, bits_to_summands, rand_gl, s3_variants,
                   summands_to_bits)
from lift import lift_models, z_verify
from sidemin import form_vec, min_side, verify_chain
from slp import greedy_slp, scheme_forms, verify_slp

IDENT = 0b100010001
TRANSVECTIONS = [IDENT | (1 << (3 * i + j))
                 for i in range(3) for j in range(3) if i != j]
BIG = 10 ** 9


def score(bits, nmodels, crestarts, seed, max_slack=2, node_cap=200_000,
          full_verify=False):
    """(total, detail) — min over sign models of exactA+exactB+heurC.
    Non-exact sides (budget/open) score BIG (the walk stays in the
    slim-sides subspace, which is where 55 lives)."""
    models = lift_models(bits, nmodels, (3, 3, 3, 23))
    if not models:
        return BIG, None
    best = (BIG, None)
    for mi, (signs, _) in enumerate(models):
        if full_verify:
            assert z_verify(bits, signs, (3, 3, 3, 23)) == 0
        fa, fb, fc = scheme_forms(bits, signs, (3, 3, 3, 23))
        va = [form_vec(f, 9) for f in fa]
        vb = [form_vec(f, 9) for f in fb]
        ra = min_side(va, 9, max_slack, node_cap)
        if ra["status"] != "exact":
            continue
        rb = min_side(vb, 9, max_slack, node_cap)
        if rb["status"] != "exact":
            continue
        if full_verify:
            verify_chain(va, 9, ra["chain"])
            verify_chain(vb, 9, rb["chain"])
        c = BIG
        for rr in range(crestarts):
            rng = random.Random(seed * 7717 + mi * 331 + rr) if rr else None
            adds, trace = greedy_slp(fc, rng)
            if full_verify:
                verify_slp(fc, trace)
            c = min(c, adds)
        tot = ra["adds"] + rb["adds"] + c
        if tot < best[0]:
            best = (tot, (ra["adds"], rb["adds"], c, mi))
    return best


def propose(cur, rng, p_local=0.85):
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

    minutes = opt("--minutes", 30, float)
    qm = opt("--quick-models", 2)
    qc = opt("--quick-crestarts", 8)
    hm = opt("--hi-models", 12)
    hc = opt("--hi-crestarts", 300)
    out = opt("--out", None, str)
    seed = opt("--rng", 1)
    jackpot = opt("--jackpot", 55)
    path = argv[0]

    s = open(path).read().split()[-1].strip()
    bits0 = [int(c) for c in s]
    assert verify_bits(bits0, 3, 3, 3, 23) == 0
    rng = random.Random(seed)

    cur = bits_to_summands(bits0)
    cur_score, _ = score(bits0, qm, qc, seed)
    best_hi, det = score(bits0, hm, hc, seed, full_verify=True)
    best_bits = bits0
    print(f"{path}: start quick={cur_score} hi={best_hi} {det}", flush=True)

    t0 = time.time()
    n = acc = 0
    while time.time() - t0 < minutes * 60:
        n += 1
        img = propose(cur, rng)
        nb = summands_to_bits(img)
        sc, _ = score(nb, qm, qc, seed + n)
        if sc < cur_score or (sc == cur_score and rng.random() < 0.5) \
                or (sc == cur_score + 1 and rng.random() < 0.03):
            acc += 1
            cur = img
            cur_score = min(cur_score, sc)
            if sc < best_hi:
                assert verify_bits(nb, 3, 3, 3, 23) == 0
                hi, det = score(nb, hm, hc, seed + n, full_verify=True)
                if hi < best_hi:
                    best_hi, best_bits = hi, nb
                    el = time.time() - t0
                    a, b, c, mi = det
                    print(f"  [{el:6.1f}s n={n}] new best hi={hi} "
                          f"= {a}+{b}+{c} (m{mi}, quick {sc})", flush=True)
                    if out:
                        open(out, "w").write(
                            "".join(map(str, best_bits)) + "\n")
                    if hi <= jackpot:
                        print(f"  *** JACKPOT: {hi} <= {jackpot} — "
                              f"verified rep saved ***", flush=True)
    print(f"{path}: done — best hi = {best_hi} "
          f"({n} proposals, {acc} accepted)", flush=True)
    if out:
        open(out, "w").write("".join(map(str, best_bits)) + "\n")
        print(f"wrote {out}", flush=True)


if __name__ == "__main__":
    main()
