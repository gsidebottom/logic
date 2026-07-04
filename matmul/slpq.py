#!/usr/bin/env python3
"""Coefficient-aware CSE (rational coefficients) for bilinear schemes.

Generalizes slp.py's signed-pair greedy to arbitrary exact rational
coefficients: a candidate subexpression is a PROJECTIVE pair — variables
(u, v) with ratio rho = coef_v / coef_u; any form containing u, v with
the same ratio can reuse w = u + rho*v (substituted with coefficient
coef_u). Cost model: binary additions/subtractions counted; unary
negation free; multiplications by fixed scalar constants NOT counted
(reported separately). This is the standard additive-complexity model
extended to non-{-1,0,1} schemes such as the AlphaEvolve-48
(Dumas-Pernet-Sedoglavic dyadic-rational form).

Every SLP is replay-verified with exact Fractions before its count is
reported.

Usage:
  python3 slpq.py --json seeds4/alphaevolve48.json [--restarts 64]
  python3 slpq.py --bits external/strassen2-4x4x49.bits --dims 4,4,4,49
      (cross-check path: +-1 schemes should match slp.py's counts)
"""
import json
import random
import sys
from fractions import Fraction
from itertools import combinations


def greedy_q(forms, rng=None):
    """ratio-pair greedy CSE over Fraction-coefficient forms.
    Returns (n_adds, trace); trace entries (w, u, rho_u=1, v, rho)."""
    forms = [dict(f) for f in forms]
    nxt = [0]
    adds = 0
    trace = []

    def canon(u, cu, v, cv):
        if str(u) > str(v):
            u, cu, v, cv = v, cv, u, cu
        return (u, v, cv / cu)

    while True:
        counts = {}
        for fi, f in enumerate(forms):
            ks = sorted(f, key=str)
            for u, v in combinations(ks, 2):
                counts.setdefault(canon(u, f[u], v, f[v]), []).append(fi)
        cands = [(cp, w) for cp, w in counts.items() if len(w) >= 2]
        if not cands:
            break
        top = max(len(w) for _, w in cands)
        tied = [(cp, w) for cp, w in cands if len(w) == top]
        (u, v, rho), where = \
            tied[rng.randrange(len(tied))] if rng else tied[0]
        w = f"W{nxt[0]}"
        nxt[0] += 1
        adds += 1
        trace.append((w, u, v, rho))
        for fi in where:
            f = forms[fi]
            if u in f and v in f and f[v] / f[u] == rho:
                cu = f[u]
                del f[u]
                del f[v]
                f[w] = f.get(w, Fraction(0)) + cu
                if f[w] == 0:
                    del f[w]
        # (stale entries simply don't substitute)
    for f in forms:
        if f:
            adds += len(f) - 1
    return adds, trace


def verify_q(orig_forms, trace):
    """expand every W symbol; re-run the same substitutions; final
    expansion must reproduce the original forms exactly."""
    expand = {}
    for (w, u, v, rho) in trace:
        eu = expand.get(u, {u: Fraction(1)})
        ev = expand.get(v, {v: Fraction(1)})
        f = {}
        for k, c in eu.items():
            f[k] = f.get(k, Fraction(0)) + c
        for k, c in ev.items():
            f[k] = f.get(k, Fraction(0)) + rho * c
        expand[w] = {k: c for k, c in f.items() if c != 0}
    forms2 = [dict(f) for f in orig_forms]
    for (w, u, v, rho) in trace:
        for f in forms2:
            if u in f and v in f and f[v] / f[u] == rho:
                cu = f[u]
                del f[u]
                del f[v]
                f[w] = f.get(w, Fraction(0)) + cu
                if f[w] == 0:
                    del f[w]
    for f0, f2 in zip(orig_forms, forms2):
        acc = {}
        for k, c in f2.items():
            for bk, bc in expand.get(k, {k: Fraction(1)}).items():
                acc[bk] = acc.get(bk, Fraction(0)) + c * bc
        acc = {k: c for k, c in acc.items() if c != 0}
        assert acc == f0, f"replay mismatch: {acc} != {f0}"
    return True


def load_json(path):
    d = json.load(open(path))
    r = d["r"]
    fa = [{k: Fraction(c) for k, c in enumerate(row) if Fraction(c) != 0}
          for row in d["alpha"]]
    fb = [{k: Fraction(c) for k, c in enumerate(row) if Fraction(c) != 0}
          for row in d["beta"]]
    n_out = len(d["gamma"][0])
    fc = []
    for pq in range(n_out):
        f = {m: Fraction(d["gamma"][m][pq]) for m in range(r)
             if Fraction(d["gamma"][m][pq]) != 0}
        fc.append(f)
    return fa, fb, fc, d.get("domain", "?")


def load_bits(path, dims):
    sys.path.insert(0, ".")
    from brent import var_counts, verify_bits
    from lift import lift
    n1, n2, n3, r = dims
    bits = [int(c) for c in open(path).read().split()[-1].strip()]
    assert verify_bits(bits, *dims) == 0
    res = lift(bits, dims)
    assert res is not None, "not liftable; no signed form"
    signs, _ = res
    na, nb, ng = var_counts(*dims)
    sa, sb, sg = n1 * n2, n2 * n3, n1 * n3
    fa = [{k: Fraction(signs[m * sa + k]) for k in range(sa)
           if bits[m * sa + k]} for m in range(r)]
    fb = [{k: Fraction(signs[na + m * sb + k]) for k in range(sb)
           if bits[na + m * sb + k]} for m in range(r)]
    fc = []
    for pq in range(sg):
        fc.append({m: Fraction(signs[na + nb + m * sg + pq])
                   for m in range(r) if bits[na + nb + m * sg + pq]})
    return fa, fb, fc, "+-1"


def main():
    argv = sys.argv[1:]

    def opt(name, default=None, cast=str):
        if name in argv:
            i = argv.index(name)
            v = cast(argv[i + 1])
            del argv[i:i + 2]
            return v
        return default

    restarts = int(opt("--restarts", 64))
    jpath = opt("--json")
    bpath = opt("--bits")
    if jpath:
        fa, fb, fc, dom = load_json(jpath)
        name = jpath
    else:
        dims = tuple(int(x) for x in opt("--dims", "4,4,4,49").split(","))
        fa, fb, fc, dom = load_bits(bpath, dims)
        name = bpath
    naive = sum(len(f) - 1 for fam in (fa, fb, fc) for f in fam if f)
    nonunit = sum(1 for fam in (fa, fb, fc) for f in fam
                  for c in f.values() if abs(c) != 1)
    best = None
    for rr in range(restarts):
        rng = random.Random(1000 + rr) if rr else None
        parts = []
        for forms in (fa, fb, fc):
            n, tr = greedy_q(forms, rng)
            verify_q(forms, tr)
            parts.append(n)
        tot = sum(parts)
        if best is None or tot < best[0]:
            best = (tot, tuple(parts))
    tot, parts = best
    print(f"{name} (coeff domain: {dom})")
    print(f"  naive adds {naive} | best CSE adds {tot} "
          f"({parts[0]}+{parts[1]}+{parts[2]}) over {restarts} restarts")
    print(f"  scalar constant multiplications in the raw scheme "
          f"(|c| not in {{0,1}}): {nonunit} (not counted as adds; "
          f"model: adds/subs counted, negation and constant "
          f"multiplication free)")


if __name__ == "__main__":
    main()
