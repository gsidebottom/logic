#!/usr/bin/env python3
"""Straight-line-program (CSE) addition counts for 3x3x23 schemes.

The additive cost of running a bilinear scheme once = the cost of an SLP
computing (i) the 23 alpha linear forms over a11..a33, (ii) the 23 beta
forms over b11..b33, (iii) the 9 output forms over M1..M23. Naive cost is
support-55; common subexpression reuse lowers it.

This implements the classic greedy signed-pair heuristic (Boyar-Peralta
flavored): repeatedly materialize the signed variable pair that occurs in
the most forms (up to a global sign), charge 1 addition, substitute; when
no pair repeats, remaining forms cost |form|-1 each. Cancellation-free =
an UPPER bound on optimal additive complexity. Signs come from lift.py's
sign-SAT (a lifted representative; other lifts may CSE differently).

Every SLP is replayed symbolically and checked to reproduce the exact
signed forms before its count is reported.

Usage: python3 slp.py scheme.bits [...]   (expects lift-able schemes)
"""
import random
import sys
from itertools import combinations

from brent import var_counts, verify_bits
from lift import DIMS3, lift_models


def scheme_forms(bits, signs, dims=DIMS3):
    """three lists of signed forms: A-forms/B-forms (over the input
    cells), C-forms (over the r product vars)."""
    n1, n2, n3, r = dims
    na, nb, ng = var_counts(*dims)
    sa, sb, sg = n1 * n2, n2 * n3, n1 * n3
    nv = na + nb + ng
    coef = [signs.get(v, 0) if bits[v] else 0 for v in range(nv)]
    aforms = [{k: coef[m * sa + k] for k in range(sa) if coef[m * sa + k]}
              for m in range(r)]
    bforms = [{k: coef[na + m * sb + k] for k in range(sb)
               if coef[na + m * sb + k]} for m in range(r)]
    cforms = []
    for pq in range(sg):
        f = {m: coef[na + nb + m * sg + pq] for m in range(r)
             if coef[na + nb + m * sg + pq]}
        cforms.append(f)
    return aforms, bforms, cforms


def greedy_slp(forms, rng=None):
    """greedy signed-pair CSE; returns (n_adds, trace) where trace allows
    replay verification. With rng, ties are broken randomly (restart
    diversity); without, deterministic."""
    forms = [dict(f) for f in forms]
    nxt = ["w", 0]
    adds = 0
    trace = []

    def canon_pair(u, su, v, sv):
        # canonical up to global sign; order by key
        if str(u) > str(v):
            u, su, v, sv = v, sv, u, su
        if su < 0:
            su, sv = -su, -sv
        return (u, su, v, sv)

    while True:
        counts = {}
        for fi, f in enumerate(forms):
            ks = sorted(f, key=str)
            for u, v in combinations(ks, 2):
                cp = canon_pair(u, f[u], v, f[v])
                counts.setdefault(cp, []).append(fi)
        cands = [(cp, w) for cp, w in counts.items() if len(w) >= 2]
        if not cands:
            break
        top = max(len(w) for _, w in cands)
        tied = [(cp, w) for cp, w in cands if len(w) == top]
        best = tied[rng.randrange(len(tied))] if rng else tied[0]
        (u, su, v, sv), where = best
        w = f"w{nxt[1]}"
        nxt[1] += 1
        adds += 1
        trace.append((w, u, su, v, sv))
        for fi in where:
            f = forms[fi]
            # the pair occurs as sigma*(su*u + sv*v)
            sigma = f[u] // su if f.get(u) == su or f.get(u) == -su else None
            if sigma is None or f.get(v) != sigma * sv:
                continue  # stale entry (form changed earlier this round)
            del f[u]
            del f[v]
            f[w] = sigma
    for f in forms:
        if len(f) >= 1:
            adds += len(f) - 1
    return adds, trace


def verify_slp(orig_forms, trace):
    """replay: expand every w in terms of base vars; re-greedy the forms
    with the same substitutions and confirm final expansion == original."""
    expand = {}
    for (w, u, su, v, sv) in trace:
        eu = expand.get(u, {u: 1})
        ev = expand.get(v, {v: 1})
        f = {}
        for k, c in eu.items():
            f[k] = f.get(k, 0) + su * c
        for k, c in ev.items():
            f[k] = f.get(k, 0) + sv * c
        expand[w] = {k: c for k, c in f.items() if c}
    # rebuild each original form through the same greedy pass
    forms2 = [dict(f) for f in orig_forms]
    for (w, u, su, v, sv) in trace:
        for f in forms2:
            if u in f and v in f:
                for sigma in (1, -1):
                    if f[u] == sigma * su and f[v] == sigma * sv:
                        del f[u]
                        del f[v]
                        f[w] = sigma
                        break
    for f0, f2 in zip(orig_forms, forms2):
        acc = {}
        for k, c in f2.items():
            for bk, bc in expand.get(k, {k: 1}).items():
                acc[bk] = acc.get(bk, 0) + c * bc
        acc = {k: c for k, c in acc.items() if c}
        assert acc == f0, f"SLP replay mismatch: {acc} != {f0}"
    return True


def best_cse(bits, nmodels=1, restarts=1, seed=0, dims=DIMS3):
    """min verified CSE adds over `nmodels` sign models x `restarts`
    randomized greedy runs (restart 0 deterministic).
    Returns (best_total, parts, model_idx) or None if unliftable."""
    models = lift_models(bits, nmodels, dims)
    if not models:
        return None
    best = None
    for mi, (signs, _) in enumerate(models):
        fa, fb, fc = scheme_forms(bits, signs, dims)
        for r in range(restarts):
            rng = random.Random(seed * 1000003 + mi * 997 + r) if r else None
            parts = []
            for forms in (fa, fb, fc):
                n, tr = greedy_slp(forms, rng)
                verify_slp(forms, tr)
                parts.append(n)
            tot = sum(parts)
            if best is None or tot < best[0]:
                best = (tot, tuple(parts), mi)
    return best


def emit_slp(bits, signs, dims, name):
    """re-run the deterministic-best greedy and print the full SLP
    (pre-additions w*, product forms, output forms), replay-verified."""
    n1, n2, n3, r = dims
    fa, fb, fc = scheme_forms(bits, signs, dims)
    out = [f"# {name}: full straight-line program, {n1}x{n2}x{n3} r={r}",
           "# cost model: binary +/- counted, unary negation free"]
    tot = 0

    def var_name(part, k):
        if part == 0:
            return f"a{k // n2 + 1}{k % n2 + 1}"
        if part == 1:
            return f"b{k // n3 + 1}{k % n3 + 1}"
        return f"M{k + 1}"

    for part, forms, label in ((0, fa, "A-side"), (1, fb, "B-side"),
                               (2, fc, "outputs")):
        best = None
        for rr in range(64):
            rng = random.Random(500 + rr) if rr else None
            n, tr = greedy_slp(forms, rng)
            verify_slp(forms, tr)
            if best is None or n < best[0]:
                best = (n, tr)
        n, tr = best
        tot += n
        out.append(f"\n## {label}: {n} additions")
        wmap = {}
        for (w, u, su, v, sv) in tr:
            un = wmap.get(u, var_name(part, u) if not str(u).startswith("w")
                          else u)
            vn = wmap.get(v, var_name(part, v) if not str(v).startswith("w")
                          else v)
            wmap[w] = w
            out.append(f"{w} = {'-' if su < 0 else ''}{un} "
                       f"{'-' if sv < 0 else '+'} {vn}")
        # remaining forms after substitutions
        forms2 = [dict(f) for f in forms]
        for (w, u, su, v, sv) in tr:
            for f in forms2:
                if u in f and v in f:
                    for sg in (1, -1):
                        if f[u] == sg * su and f[v] == sg * sv:
                            del f[u]
                            del f[v]
                            f[w] = sg
                            break
        for fi, f in enumerate(forms2):
            terms = []
            for k, c in sorted(f.items(), key=lambda kv: str(kv[0])):
                nm = k if str(k).startswith("w") else var_name(part, k)
                terms.append(f"{'-' if c < 0 else '+'}{nm}")
            lhs = (f"P{fi + 1}" if part == 0 else
                   f"Q{fi + 1}" if part == 1 else
                   f"C{fi // n3 + 1}{fi % n3 + 1}")
            out.append(f"{lhs} = {' '.join(terms)}"
                       + ("" if part == 2 else
                          f"   # M{fi + 1} = P{fi + 1} * Q{fi + 1}"
                          if part == 0 else ""))
    out.append(f"\n# TOTAL: {tot} additions (+ {r} multiplications "
               f"M_i = P_i * Q_i)")
    return "\n".join(out) + "\n", tot


def main():
    argv = sys.argv[1:]

    def opt(name, default):
        if name in argv:
            i = argv.index(name)
            val = int(argv[i + 1])
            del argv[i:i + 2]
            return val
        return default

    nmodels = opt("--models", 1)
    restarts = opt("--restarts", 1)
    emit = None
    if "--emit" in argv:
        i = argv.index("--emit")
        emit = argv[i + 1]
        del argv[i:i + 2]
    dims = DIMS3
    if "--dims" in argv:
        i = argv.index("--dims")
        dims = tuple(int(x) for x in argv[i + 1].split(","))
        del argv[i:i + 2]
    n1, n2, n3, r = dims
    # naive adds = support - (2r + n1*n3): r products x (|a|-1)+(|b|-1),
    # n1*n3 outputs x (contributing-1)
    naive_off = 2 * r + n1 * n3
    print(f"{'scheme':26s} {'support':>7s} {'naive':>5s} "
          f"{'best-CSE':>8s}  (A+B+C, model#)   "
          f"[{nmodels} sign models x {restarts} restarts, dims {dims}]")
    for path in argv:
        s = open(path).read().split()[-1].strip()
        bits = [int(c) for c in s]
        assert verify_bits(bits, *dims) == 0
        res = best_cse(bits, nmodels, restarts, dims=dims)
        if res is None:
            print(f"{path}: not liftable, skipped")
            continue
        tot, parts, mi = res
        sup = sum(bits)
        name = path.split("/")[-1]
        print(f"{name:26s} {sup:7d} {sup - naive_off:5d} {tot:8d}  "
              f"({parts[0]}+{parts[1]}+{parts[2]}, m{mi})", flush=True)
        if emit:
            models = lift_models(bits, nmodels, dims)
            signs = models[mi][0]
            txt, etot = emit_slp(bits, signs, dims, name)
            open(emit, "w").write(txt)
            print(f"  emitted {etot}-addition SLP -> {emit}", flush=True)


if __name__ == "__main__":
    main()
