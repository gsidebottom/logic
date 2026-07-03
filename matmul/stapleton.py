#!/usr/bin/env python3
"""Reconstruct, classify, and re-optimize the Stapleton 60-addition
rank-23 scheme (arXiv:2508.03857v1, github.com/Joshua-Stapleton/
60_addition_rank_23_scheme).

Reconstruction: symbolically expand the paper's SLP (Appendix A) to
recover the bilinear tensors (alpha, beta, gamma with signs), then
  - verify mod-2 against the Brent equations and exactly over Z,
  - emit our 621-bit form (external/stapleton60.bits),
  - classify vs our 53 finds and the full HKS DB (fingerprint + exact),
  - run our CSE optimizer on it (his signs + fresh sign-SAT models).

Usage: python3 stapleton.py [--models K --restarts R]
"""
import os
import sys
from collections import defaultdict

from brent import var_counts, verify_bits
from equiv import bits_to_summands, equivalent, fingerprint, s3_variants
from lift import z_verify
from slp import greedy_slp, scheme_forms, verify_slp

NA, NB, NG = var_counts(3, 3, 3, 23)


def build():
    """expand the paper's SLP; returns (aforms, bforms, gcoef) where
    aforms[m]: dict a-cell(0..8)->coef, bforms[m]: dict b-cell->coef,
    gcoef[m]: dict c-cell(0..8)->coef."""
    def lin(i):
        return {i: 1}

    def add(x, y, s=1):
        d = defaultdict(int, x)
        for k, c in y.items():
            d[k] += s * c
        return {k: c for k, c in d.items() if c}

    def neg(x):
        return {k: -c for k, c in x.items()}

    A = [lin(i) for i in range(9)]
    B = [lin(i) for i in range(9)]
    A0, A1, A2, A3, A4, A5, A6, A7, A8 = A
    B0, B1, B2, B3, B4, B5, B6, B7, B8 = B

    prods = []

    def MU(x, y):
        prods.append((dict(x), dict(y)))
        return {len(prods) - 1: 1}  # symbol: product index -> coef

    AD = add  # over either base forms or product-symbol forms

    # --- pre-additions (12) ---
    t0 = AD(A0, A3, -1); t1 = AD(A4, A5); t2 = AD(A6, A8); t3 = AD(A1, A2)
    t4 = AD(A7, t1, -1); t5 = AD(t0, t2)
    u0 = AD(B0, B2, -1); u1 = AD(B4, B7, -1); u2 = AD(B1, u0)
    u3 = AD(B5, B8, -1); u4 = AD(B6, u3); u5 = AD(u1, u2)

    # --- products (23) ---
    M0 = MU(neg(t3), neg(B7))
    M1 = MU(AD(AD(neg(A3), A4), A7, -1), neg(u1))
    M2 = MU(AD(A1, A3, -1), u5)
    M3 = MU(neg(t0), neg(u0))
    M4 = MU(neg(A5), u3)
    M5 = MU(AD(A8, t4), B7)
    M6 = MU(neg(A8), AD(AD(neg(B2), B7), B8))
    M7 = MU(t4, AD(B5, B7))
    M8 = MU(neg(A7), neg(B3))
    M9 = MU(AD(A1, A5), neg(u4))
    M10 = MU(neg(t5), AD(B2, B6, -1))
    M11 = MU(neg(A6), B1)
    M12 = MU(AD(AD(A2, A5, -1), t5), neg(B6))
    M13 = MU(AD(neg(A0), A1), u2)
    M14 = MU(neg(A3), B2)
    M15 = MU(AD(A6, t0), AD(B0, B6, -1))
    M16 = MU(A7, AD(B4, B5))
    M17 = MU(t3, AD(neg(B6), B8))
    M18 = MU(neg(t2), B2)
    M19 = MU(neg(A1), AD(AD(neg(B3), u4), u5, -1))
    M20 = MU(AD(neg(A1), A4), B3)
    M21 = MU(neg(t1), neg(B5))
    M22 = MU(A3, AD(B1, u1))

    # --- v-aggregates + outputs, as combos of product symbols ---
    v0 = AD(M4, M14, -1); v1 = AD(M2, M22); v2 = AD(M7, M21)
    v3 = AD(M9, v0, -1); v4 = AD(M10, M18, -1); v5 = AD(M3, v1, -1)
    v6 = AD(M5, v2, -1); v7 = AD(M12, v3); v8 = AD(v4, v7)
    C0 = AD(AD(M19, v5), v8, -1)
    C1 = AD(AD(M0, M13, -1), v5, -1)
    C2 = AD(M17, v8, -1)
    C3 = AD(AD(AD(M19, M20), v1, -1), v3, -1)
    C4 = AD(AD(AD(neg(M1), M16), M22), v2, -1)
    C5 = AD(M21, v0)
    C6 = AD(AD(AD(neg(M3), M8), M15), v4)
    C7 = AD(AD(neg(M11), M16), v6)
    C8 = AD(AD(neg(M6), M18, -1), v6, -1)

    Cs = [C0, C1, C2, C3, C4, C5, C6, C7, C8]
    aforms = [p[0] for p in prods]
    bforms = [p[1] for p in prods]
    gcoef = [defaultdict(int) for _ in range(23)]
    for c_cell, form in enumerate(Cs):
        for m, coef in form.items():
            gcoef[m][c_cell] += coef
    gcoef = [{k: c for k, c in g.items() if c} for g in gcoef]
    return aforms, bforms, gcoef


def to_bits_signs(aforms, bforms, gcoef):
    bits = [0] * 621
    signs = {}
    for m in range(23):
        for cell, c in aforms[m].items():
            assert c in (1, -1), (m, cell, c)
            v = m * 9 + cell
            bits[v] = 1
            signs[v] = c
        for cell, c in bforms[m].items():
            assert c in (1, -1)
            v = NA + m * 9 + cell
            bits[v] = 1
            signs[v] = c
        for cell, c in gcoef[m].items():
            assert c in (1, -1)
            v = NA + NB + m * 9 + cell
            bits[v] = 1
            signs[v] = c
    return bits, signs


def main():
    argv = sys.argv[1:]

    def opt(name, default):
        if name in argv:
            i = argv.index(name)
            val = int(argv[i + 1])
            del argv[i:i + 2]
            return val
        return default

    nmodels = opt("--models", 16)
    restarts = opt("--restarts", 64)

    aforms, bforms, gcoef = build()
    bits, signs = to_bits_signs(aforms, bforms, gcoef)
    assert verify_bits(bits, 3, 3, 3, 23) == 0, "mod-2 Brent FAILS"
    assert z_verify(bits, signs) == 0, "integer Brent FAILS"
    sup = sum(bits)
    print(f"stapleton60 reconstructed: VERIFIED mod-2 + exactly over Z; "
          f"support {sup} (naive adds {sup - 55})")
    os.makedirs("external", exist_ok=True)
    open("external/stapleton60.bits", "w").write(
        "".join(map(str, bits)) + "\n")

    # --- classification vs our finds + full DB ---
    summ = bits_to_summands(bits)
    fps = {fingerprint(v) for v in s3_variants(summ)}
    hits = []
    for ln in open("dbcache/all_schemes.txt"):
        name, bs = ln.split()
        s2 = bits_to_summands([int(c) for c in bs])
        if fingerprint(s2) in fps:
            hits.append((name, s2))
    print(f"DB fingerprint collisions: {len(hits)}"
          + (f" ({[n for n, _ in hits][:5]})" if hits else ""))
    verdict = "NEW vs DB"
    for name, s2 in hits:
        if equivalent(summ, s2):
            verdict = f"EQUIVALENT to DB {name}"
            break
    print(f"stapleton60 vs full HKS DB: {verdict}")
    import glob
    for p in sorted(glob.glob("found/walk-*.bits")):
        s2 = bits_to_summands(
            [int(c) for c in open(p).read().strip()])
        if fingerprint(s2) in fps and equivalent(summ, s2):
            print(f"  EQUIVALENT to our {p}")
            break
    else:
        print("  inequivalent to all our walk finds")

    # --- our optimizer on his scheme ---
    import random
    from lift import lift_models
    fa, fb, fc = scheme_forms(bits, signs)
    best = None
    sign_sets = [("paper", signs)]
    sign_sets += [(f"m{i}", s) for i, (s, _) in
                  enumerate(lift_models(bits, nmodels))]
    for label, sg in sign_sets:
        fa, fb, fc = scheme_forms(bits, sg)
        for r in range(restarts):
            rng = random.Random(9000 + r) if r else None
            parts = []
            for forms in (fa, fb, fc):
                n, tr = greedy_slp(forms, rng)
                verify_slp(forms, tr)
                parts.append(n)
            tot = sum(parts)
            if best is None or tot < best[0]:
                best = (tot, tuple(parts), label)
    tot, parts, label = best
    print(f"our optimizer on stapleton60: best {tot} adds "
          f"({parts[0]}+{parts[1]}+{parts[2]}, signs={label}) "
          f"[paper: 60]")


if __name__ == "__main__":
    main()
