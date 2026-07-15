#!/usr/bin/env python3
"""machopt — machine-cost wire-exponent optimizer for a rank-48 4x4
SLP triple. Moves: relabel P-internal wires by 2^e and pre-scale each
product t by 2^{s_t} (absorbed into L's output-t line; P's i_t terms
compensate). Objective: machinecost DELAYED cycles of the whole
triple — the goal is clearing P's halvings so its outputs become
delayed-reduction eligible, even at the price of extra L-side shifts.
Every improving incumbent is gated by Fraction evaluation of the
relabeled triple against plain 4x4 matmul on random rationals (the
same composition convention bench284r field-gates). Parallel
restarts via multiprocessing. Usage:
  machopt.py L.slp R.slp P.slp out_prefix [restarts] [workers]
Emits out_prefix_{L,R,P}.slp for the best gated incumbent.
"""
import random
import sys
from fractions import Fraction
from multiprocessing import Pool

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import machinecost as mc

C = mc  # cost constants live there


def adjusted(ops, ewires, leafshift, outshift):
    """Rewrite term exponents under wire relabels. ewires: {vname: e}
    (wire w carries 2^{e_w} x true value; outputs pinned e=0 by
    construction). leafshift: {leafname: s} (leaf arrives pre-scaled
    by 2^s). outshift: {out_name: s} add s to every term of that
    output's line (used to make L emit 2^{s_t} x row t)."""
    out = []
    for v, o, terms in ops:
        ev = ewires.get(v, 0)
        extra = outshift.get(o, 0) if o else 0
        nt = []
        for (sg, src, k, odd) in terms:
            es = ewires.get(src, 0) + leafshift.get(src, 0)
            nt.append((sg, src, k + ev + extra - es, odd))
        out.append((v, o, nt))
    return out


def triple_cost(L, R, P, s, eP):
    """returns (true delayed cycles, shaped objective, eligible outs).
    Shaping bridges the eligibility plateau: each remaining negative
    exponent or odd const in P costs 3.0 extra in the shaped score, so
    descent clears halvings one at a time even though delayability
    only flips per whole output-DAG."""
    Ladj = adjusted(L, {f"o{t}": s[t] for t in range(48)}, {}, {})
    Padj = adjusted(P, eP, {f"i{t}": s[t] for t in range(48)}, {})
    lc = mc.scalar_cost(Ladj) + mc.scalar_cost(R)
    pdc, ne, no, nb, npe = mc.p_delayed(Padj)
    dl = lc + npe * mc.D_MUL + (48 - npe) * mc.C_MUL + pdc
    blockers = sum(
        1 for (_, _, t) in Padj for (_, _, k, odd) in t if k < 0 or odd != 1
    )
    return dl, dl + 3.0 * blockers, ne


def fr_eval(ops, inputs):
    """Evaluate parsed ops over Fractions. inputs: {leaf: Fraction}."""
    env = dict(inputs)
    outs = {}
    for v, o, terms in ops:
        acc = Fraction(0)
        for (sg, src, k, odd) in terms:
            x = env[src]
            if odd != 1:
                x = x * odd if odd > 0 else x / (-odd)
            x = x * Fraction(2) ** k
            acc += sg * x
        env[v] = acc
        if o:
            outs[o] = acc
    return outs


def gate(L, R, P, s, eP, trials=10, seed=7):
    rng = random.Random(seed)
    Ladj = adjusted(L, {f"o{t}": s[t] for t in range(48)}, {}, {})
    Padj = adjusted(P, eP, {f"i{t}": s[t] for t in range(48)}, {})
    for _ in range(trials):
        a = [Fraction(rng.randint(-99, 99), rng.randint(1, 9)) for _ in range(16)]
        b = [Fraction(rng.randint(-99, 99), rng.randint(1, 9)) for _ in range(16)]
        la = fr_eval(Ladj, {f"i{i}": a[i] for i in range(16)})
        rb = fr_eval(R, {f"i{i}": b[i] for i in range(16)})
        pr = {f"i{t}": la[f"o{t}"] * rb[f"o{t}"] for t in range(48)}
        co = fr_eval(Padj, pr)
        for i in range(4):
            for j in range(4):
                want = sum(a[4 * i + k] * b[4 * k + j] for k in range(4))
                if co[f"o{4 * i + j}"] != want:
                    return False
    return True


def flatten_cols(P):
    """Per-product max denominator exponent over the flattened
    (CSE-expanded) P coefficient matrix."""
    coef = {}  # vname -> {leaf: exponent-min tracker}
    need = [0] * 48
    exps = {}  # vname -> {leaf: set of exponents}
    for v, o, terms in P:
        cur = {}
        for (sg, src, k, odd) in terms:
            if src in exps:
                for lf, es in exps[src].items():
                    cur.setdefault(lf, set()).update(e + k for e in es)
            else:
                cur.setdefault(src, set()).add(k)
        exps[v] = cur
        if o and o.startswith("o"):
            for lf, es in cur.items():
                t = int(lf[1:])
                need[t] = max(need[t], -min(es))
    return need


def push_forward(P, s):
    """Choose internal-wire relabels by forward deficit-push: after
    leaf prescale s, set e_w so w's own line has nonneg exponents
    (pushing any remaining deficit to consumers; outputs stay pinned
    and keep whatever deficit survives)."""
    eP = {}
    ls = {f"i{t}": s[t] for t in range(48)}
    for v, o, terms in P:
        if o and o.startswith("o"):
            continue
        lo = min(
            (k - ls.get(src, 0) - eP.get(src, 0) for (sg, src, k, odd) in terms),
            default=0,
        )
        if lo < 0:
            eP[v] = lo  # wire carries 2^lo x true value
    return eP


def restart(args):
    paths, rid = args
    L, R, P = (mc.parse(p) for p in paths)
    pw = [v for (v, o, _) in P if not (o and o.startswith("o"))]
    rng = random.Random(1000 + rid)
    s = [0] * 48
    eP = {}
    if rid == 1:
        s = flatten_cols(P)
        eP = push_forward(P, s)
    elif rid > 1:
        s = [rng.choice([-1, 0, 0, 0, 1]) for _ in range(48)]
        eP = {w: rng.choice([-1, 0, 0, 1]) for w in pw}
    _, best, _ = triple_cost(L, R, P, s, eP)
    for _ in range(60):
        improved = False
        for t in range(48):
            cur = s[t]
            for v in range(-3, 4):
                if v == cur:
                    continue
                s[t] = v
                _, c, _ = triple_cost(L, R, P, s, eP)
                if c < best:
                    best, cur, improved = c, v, True
            s[t] = cur
        for w in pw:
            cur = eP.get(w, 0)
            for v in range(-3, 4):
                if v == cur:
                    continue
                eP[w] = v
                _, c, _ = triple_cost(L, R, P, s, eP)
                if c < best:
                    best, cur, improved = c, v, True
            eP[w] = cur
        if not improved:
            break
    ok = gate(L, R, P, s, eP)
    true, _, ne = triple_cost(L, R, P, s, eP)
    return (true if ok else 1e9, ne, s, eP, rid, ok)


def emit(ops, path):
    lines = []
    for v, o, terms in ops:
        parts = []
        for (sg, src, k, odd) in terms:
            t = src
            if odd != 1:
                t += f"*{odd}" if odd > 0 else f"/{-odd}"
            if k > 0:
                t += f"*{2**k}"
            elif k < 0:
                t += f"/{2**(-k)}"
            parts.append(("-" if sg < 0 else ("+" if parts else "")) + t)
        name = o if o else v
        lines.append(f"{name}:={''.join(parts)};")
    open(path, "w").write("\n".join(lines) + "\n")


def main():
    lp, rp, pp, pre = sys.argv[1:5]
    restarts = int(sys.argv[5]) if len(sys.argv) > 5 else 64
    workers = int(sys.argv[6]) if len(sys.argv) > 6 else 8
    L, R, P = mc.parse(lp), mc.parse(rp), mc.parse(pp)
    base, _, ne0 = triple_cost(L, R, P, [0] * 48, {})
    print(f"baseline delayed {base:.1f} (P eligible outputs {ne0}/16)", flush=True)
    with Pool(workers) as pool:
        results = pool.map(restart, [((lp, rp, pp), r) for r in range(restarts)])
    results.sort(key=lambda x: x[0])
    bc, ne, s, eP, rid, ok = results[0]
    print(f"best gated {bc:.1f} (restart {rid}, P eligible {ne}/16, gate {ok})")
    if bc < base and ok:
        Ladj = adjusted(L, {f"o{t}": s[t] for t in range(48)}, {}, {})
        Padj = adjusted(P, eP, {f"i{t}": s[t] for t in range(48)}, {})
        emit(Ladj, f"{pre}_L.slp")
        emit(R, f"{pre}_R.slp")
        emit(Padj, f"{pre}_P.slp")
        print(f"emitted {pre}_{{L,R,P}}.slp  (delayed {base:.1f} -> {bc:.1f})")
    else:
        print("no gated improvement over baseline")


if __name__ == "__main__":
    main()
