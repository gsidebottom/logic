#!/usr/bin/env python3
"""Gauge-canonical forms for sign models of a 3x3x23 mask scheme.

The diagonal sandwich gauges (p, q, r) in ({+-1}^3)^3 act on a sign
model by flipping alpha entry (m, i, j) by p_i*q_j, beta (m, j, k) by
q_j*r_k and gamma (m, i, k) by p_i*r_k -- wait: gamma indexes output
cell (p_out, q_out) = C[i][k]; its flip is p_i*r_k.  Composed with the
per-product gauge (flipping (u_m, w_m) or (v_m, w_m) together), models
in one orbit are the same integer scheme up to re-signing of the
coordinate axes, and all searches (leg minima, liftability, conversion
costs) coincide on an orbit.  `canonical` returns the lexicographic
minimum over the 512 diagonal gauges, each followed by lift.py's
per-product normalization (first alpha and first beta support bit of
each product forced +1), so canonical forms are directly comparable
with lift_models output.

Gate discipline (cf. the ported-action lesson): the self-test asserts
(1) every gauged model still z-verifies the signed Brent equations --
the action fixes the object; (2) canonical(model) ==
canonical(gauge(model)) for random gauges; (3) normalization is
idempotent.

Usage as a module: from gaugecanon import canonical, dedup_models
Self-test: gaugecanon.py selftest bits-file
"""
import itertools, sys

NA = 207


def blocks_of(v):
    """var index -> (block, m, x, y) with x, y in 0..2."""
    if v < NA:
        m, c = divmod(v, 9)
        return 0, m, c // 3, c % 3
    if v < 2 * NA:
        m, c = divmod(v - NA, 9)
        return 1, m, c // 3, c % 3
    m, c = divmod(v - 2 * NA, 9)
    return 2, m, c // 3, c % 3


def apply_gauge(signs, p, q, r):
    out = {}
    for v, s in signs.items():
        b, _, x, y = blocks_of(v)
        if b == 0:
            f = p[x] * q[y]
        elif b == 1:
            f = q[x] * r[y]
        else:
            f = p[x] * r[y]
        out[v] = s * f
    return out


def normalize(signs, bits):
    """lift.py's per-product convention: first alpha support bit and
    first beta support bit of every product +1 (flipping (u,w) resp.
    (v,w) pairs, which preserves the signed Brent equations)."""
    out = dict(signs)
    for m in range(23):
        a0 = next(v for v in range(m * 9, m * 9 + 9) if bits[v])
        if out[a0] < 0:
            for v in range(m * 9, m * 9 + 9):
                if bits[v]:
                    out[v] = -out[v]
            for v in range(2 * NA + m * 9, 2 * NA + m * 9 + 9):
                if bits[v]:
                    out[v] = -out[v]
        b0 = next(v for v in range(NA + m * 9, NA + m * 9 + 9) if bits[v])
        if out[b0] < 0:
            for v in range(NA + m * 9, NA + m * 9 + 9):
                if bits[v]:
                    out[v] = -out[v]
            for v in range(2 * NA + m * 9, 2 * NA + m * 9 + 9):
                if bits[v]:
                    out[v] = -out[v]
    return out


def canonical(signs, bits):
    best = None
    for pp in itertools.product((1, -1), repeat=3):
        for qq in itertools.product((1, -1), repeat=3):
            for rr in itertools.product((1, -1), repeat=3):
                cand = tuple(sorted(normalize(apply_gauge(signs, pp, qq, rr),
                                              bits).items()))
                if best is None or cand < best:
                    best = cand
    return best


def dedup_models(models, bits, verbose=True):
    """keep the first model of each gauge orbit; returns the sublist."""
    seen, out = set(), []
    for pair in models:
        c = canonical(pair[0], bits)
        if c not in seen:
            seen.add(c)
            out.append(pair)
    if verbose:
        print(f"gauge dedup: {len(models)} models -> {len(out)} orbits",
              flush=True)
    return out


if __name__ == "__main__":
    assert sys.argv[1] == "selftest"
    import random
    sys.path.insert(0, __file__.rsplit("/", 1)[0])
    from lift import lift_models, z_verify
    bits = [int(c) for c in open(sys.argv[2]).read().split()[-1].strip()]
    DIMS = (3, 3, 3, 23)
    models = lift_models(bits, 6, DIMS)
    assert models, "no models"
    for mi, (signs, _) in enumerate(models):
        # gate 1: random gauges preserve validity (action fixes the object)
        for _ in range(8):
            g = [tuple(random.choice((1, -1)) for _ in range(3)) for _ in range(3)]
            gs = apply_gauge(signs, *g)
            assert z_verify(bits, gs, DIMS) == 0, "gauged model fails Brent"
            # gate 2: canonical is gauge-invariant
            assert canonical(gs, bits) == canonical(signs, bits), \
                "canonical not gauge-invariant"
        # gate 3: normalization idempotent
        n1 = normalize(signs, bits)
        assert normalize(n1, bits) == n1
    d = dedup_models(models, bits)
    print(f"selftest PASS ({len(models)} models, {len(d)} orbits)")
