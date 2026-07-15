#!/usr/bin/env python3
"""machinecost — score rank-48 4x4 SLP triples (L,R,P) under a MACHINE
cost model instead of raw add count: shift-based dyadics, and the F_p
analogue of mult-add fusion = DELAYED REDUCTION (accumulate products
as (lo,hi) u64 pairs, one reduction per output) on the P side.

Model (Apple-M-class scalar Goldilocks, coarse cycle estimates — the
point is RANKING schemes, not absolute cycles; constants are stated):
  add/sub (branchless mod)           1.5
  x2^k    (k modular doublings)      min(1.5k, CMUL)
  /2^k    (k halvings, shift+fixup)  min(2.0k, CMUL)
  small odd const-mul (3,5,7,...)    4.5   (shift+add chain)
  general const-mul / product mul    6.5   (mul+umulh+reduce128)
  --- delayed-reduction path (P side) ---
  product mul, reduction deferred    2.0   (mul+umulh only)
  accumulate +-term into (lo,hi)     2.0   (adds+adcs)
  shift accumulator by 2^k (k>0)     2.5
  final combine + reduce per output  7.0
  reduce at eligible/non-eligible boundary  5.0
Eligibility: a P node can delay iff every source is a product or an
eligible node and every scale is x2^k (k>=0). /2 breaks it (cannot
halve an unreduced pair without parity); odd consts break it (v1).
A value needed by BOTH worlds pays one boundary reduce.
SWAR/NEON lanes are NOT scheme-dependent: lanes come from batching
independent tiles (2x64 Goldilocks NEON ~parity; 4x32 BabyBear wins
~2-3x) and scale every scheme equally, so they don't reorder the
ranking. Usage:
  machinecost.py L.slp R.slp P.slp [label]     one triple
  machinecost.py --sweep dir                   all *_L/_R/_P triples
"""
import os
import re
import sys

LINE = re.compile(r"^\s*(\w+)\s*:=\s*(.+?);\s*$")
INPUT = re.compile(r"^i\d+$")

C_ADD, C_MUL, C_ODD = 1.5, 6.5, 4.5
C_DBL, C_HALF = 1.5, 2.0
D_MUL, D_ACC, D_SHIFT, D_COMB, C_RED = 2.0, 2.0, 2.5, 7.0, 5.0


def parse(path):
    """ops: list of (vname, out_name_or_None, [(sign, src, k, odd)]).
    SSA versioning: reassignment mints a new vname; refs resolve to the
    version current at that line. Zero literals propagate and vanish.
    Terms: sign in +-1, src = versioned name or input, k = net dyadic
    exponent, odd = residual odd multiplier (1 = none)."""
    ops, env, ver, zero = [], {}, {}, set()

    def scale(s, j):
        k, odd = 0, 1
        while j < len(s) and s[j] in "*/":
            mm = re.match(r"([*/])(\d+)", s[j:])
            c = int(mm.group(2))
            e = 0
            while c % 2 == 0:
                c //= 2
                e += 1
            if mm.group(1) == "*":
                k += e
                odd *= c
            else:
                k -= e
                if c != 1:
                    odd *= -c  # odd inverse: full const-mul, not delayable
            j += mm.end()
        return k, odd, j

    def pexpr(s, sink):
        terms, i, sign, n = [], 0, 1, len(s)
        while i < n:
            c = s[i]
            if c == "+":
                sign, i = 1, i + 1
                continue
            if c == "-":
                sign, i = -1, i + 1
                continue
            if c == "(":
                jc = find_close(s, i)
                k, odd, j = scale(s, jc + 1)
                v = f"__v{len(ops)}"
                gt = pexpr(s[i + 1 : jc], v)
                ops.append((v, None, gt))
                if not gt:
                    zero.add(v)
                else:
                    terms.append((sign, v, k, odd))
                sign, i = 1, j
                continue
            m = re.match(r"(\w+)", s[i:])
            src = m.group(1)
            i += m.end()
            k, odd, i = scale(s, i)
            if src.isdigit():
                if int(src) != 0:
                    raise ValueError(f"literal {src}")
                sign = 1
                continue
            v = env.get(src, src)
            if v not in zero:
                terms.append((sign, v, k, odd))
            sign = 1
        return terms

    def find_close(s, i):
        d, j = 1, i + 1
        while j < len(s) and d:
            d += s[j] == "("
            d -= s[j] == ")"
            j += 1
        return j - 1

    for ln in open(path):
        m = LINE.match(ln)
        if not m:
            continue
        name, expr = m.groups()
        terms = pexpr(expr.replace(" ", ""), name)
        ver[name] = ver.get(name, -1) + 1
        v = f"{name}.{ver[name]}" if ver[name] else name
        env[name] = v
        ops.append((v, name, terms))
        if not terms:
            zero.add(v)
    return ops


def dims(ops):
    ins = set()
    outs = set()
    for _, out, terms in ops:
        for _, src, _, _ in terms:
            if INPUT.match(src):
                ins.add(src)
        if out and out.startswith("o"):
            outs.add(out)
    return len(ins), len(outs)


def counts(ops):
    a = sh = 0
    for _, _, terms in ops:
        a += max(0, len(terms) - 1)
        sh += sum(1 for (_, _, k, odd) in terms if k or odd != 1)
    return a, sh


def term_cost(k, odd):
    c = 0.0
    if odd != 1:
        c += C_ODD if 1 < odd <= 15 else C_MUL
    if k > 0:
        c += min(C_DBL * k, C_MUL)
    elif k < 0:
        c += min(C_HALF * (-k), C_MUL)
    return c


def scalar_cost(ops):
    return sum(
        max(0, len(t) - 1) * C_ADD + sum(term_cost(k, o) for (_, _, k, o) in t)
        for (_, _, t) in ops
    )


def p_delayed(ops):
    """Delayed-reduction cost of a P network; returns
    (cost, eligible_outputs, outputs, boundary_reduces)."""
    defs = {v: t for (v, _, t) in ops}
    elig = {}
    for v, _, terms in ops:  # ops are in def order: no recursion needed
        elig[v] = bool(terms) and all(
            k >= 0 and o == 1 and (INPUT.match(s) or elig.get(s, False))
            for (_, s, k, o) in terms
        )
    pe = set()  # products actually deferred (have an eligible consumer)
    for v, _, terms in ops:
        if elig[v]:
            pe.update(s for (_, s, _, _) in terms if INPUT.match(s))
    boundary = set()
    for v, _, terms in ops:
        if not elig[v]:
            for _, s, _, _ in terms:
                if (INPUT.match(s) and s in pe) or elig.get(s, False):
                    boundary.add(s)
    cost, ne, no = 0.0, 0, 0
    for v, out, terms in ops:
        is_out = out is not None and out.startswith("o")
        if elig[v]:
            cost += max(0, len(terms) - 1) * D_ACC
            cost += sum(D_SHIFT for (_, _, k, _) in terms if k > 0)
            if is_out:
                cost += D_COMB
                ne += 1
        else:
            cost += max(0, len(terms) - 1) * C_ADD
            cost += sum(term_cost(k, o) for (_, _, k, o) in terms)
        no += is_out
    return cost + len(boundary) * C_RED, ne, no, len(boundary), len(pe)


def score(lp, rp, pp, label, only44=False):
    L, R, P = parse(lp), parse(rp), parse(pp)
    (lin, lout), (rin, rout), (pin, pout) = dims(L), dims(R), dims(P)
    if only44 and not (lin == rin == 16 and lout == rout == 48 and pout == 16):
        return None
    nprod = lout
    la, ls = counts(L)
    ra, rs = counts(R)
    pa, ps = counts(P)
    sc = scalar_cost(L) + scalar_cost(R) + nprod * C_MUL + scalar_cost(P)
    pdc, ne, no, nb, npe = p_delayed(P)
    # only products with an eligible consumer defer their reduction;
    # the rest are computed reduced as in the scalar path.
    dl = (scalar_cost(L) + scalar_cost(R) + npe * D_MUL
          + (nprod - npe) * C_MUL + pdc)
    print(
        f"{label:36s} adds {la + ra + pa:4d}  sh {ls + rs + ps:3d}  "
        f"scalar {sc:7.1f}  delayed {dl:7.1f}  "
        f"(P {ne}/{no} delayable, {nb} boundary-red)"
    )
    return dl


def naive_baseline():
    sc = 64 * C_MUL + 48 * C_ADD
    dl = 64 * (D_MUL + D_ACC) + 16 * D_COMB
    print(
        f"{'naive 4x4 (baseline)':36s} adds   48  sh   0  "
        f"scalar {sc:7.1f}  delayed {dl:7.1f}  (16/16 dot products delayable)"
    )


def main():
    if sys.argv[1] == "--sweep":
        naive_baseline()
        root = sys.argv[2]
        trips = []
        for dp, _, fs in os.walk(root):
            for f in fs:
                if f.endswith("_L.slp"):
                    b = f[:-6]
                    if f"{b}_R.slp" in fs and f"{b}_P.slp" in fs:
                        trips.append((dp, b, "_"))
            if "L.slp" in fs and "R.slp" in fs and "P.slp" in fs:
                trips.append((dp, "", ""))
        for dp, b, sep in sorted(trips):
            paths = [os.path.join(dp, f"{b}{sep}{s}.slp") for s in "LRP"]
            lbl = (os.path.relpath(dp, root) + "/" + b)[-36:]
            try:
                score(*paths, lbl, only44=True)
            except Exception as e:
                print(f"{lbl:36s} SKIP ({e})")
    else:
        naive_baseline()
        score(sys.argv[1], sys.argv[2], sys.argv[3],
              sys.argv[4] if len(sys.argv) > 4 else "triple")


if __name__ == "__main__":
    main()
