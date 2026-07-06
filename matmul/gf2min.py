#!/usr/bin/env python3
"""Exact GF(2) XOR-chain covering and a model-independent C-side bound.

`gf2_min_cover(targets, nbase)` — minimum number of XOR operations so
that one chain over the `nbase` unit vectors contains every target
(weight-<=1 targets and duplicates are free).  This is sidemin.min_side
ported to GF(2): vectors become bitmasks, +/- collapse to XOR, signs
disappear.  Same IDDFS on helper count with the closure normal form
(cover any derivable target immediately; branch only on helpers) —
the exchange argument for completeness carries over verbatim, and the
`selftest` re-validates it against exhaustive search on small cases.

`c_gf2_exact(bits)` — the exact GF(2) additive complexity of a scheme's
C side, via the transposition principle over GF(2):
    A(W) = A(W^T) + (inputs - outputs) = gf2_min_cover(W^T rows) + r - 9.
W's support is the gamma bits alone, so this is per-representative —
NO sign-model loop.  Reducing any integer +-SLP mod 2 gives an XOR SLP
of no greater size, so for EVERY sign model of the representative:
    C_Z(model) >= C_GF2,   sides_Z(model) >= sides_GF2.
Hence  sides_GF2 + C_GF2 <= total_Z(model)  for every model — a sound,
model-exhaustive filter for "could this representative host a 54?".

CLI:
  gf2min.py selftest
  gf2min.py sweep LIST.txt [--cutoff 54]   # LIST = .bits paths, one/line;
      reads GF2 sides from the -sNN- filename tag, prints every rep with
      sides_GF2 + C_GF2 <= cutoff, plus a summary.
"""
import re
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from slp import scheme_forms
from tcmin import c_transpose_rows

DIMS = (3, 3, 3, 23)


class Budget(Exception):
    pass


def gf2_min_cover(targets, nbase, max_slack=6, node_cap=20_000_000):
    """min #XORs so a chain over the nbase unit vectors covers all
    targets.  Returns dict with nt, h, adds, chain, status, nodes;
    on 'budget'/'open', adds is a LOWER bound and chain is None."""
    tset = sorted({t for t in targets if bin(t).count("1") >= 2})
    nt = len(tset)
    nodes = [0]
    base = [1 << i for i in range(nbase)]

    def close(pool_list, pool_set, uncovered, order):
        progress = True
        while progress:
            progress = False
            for t in list(uncovered):
                for x in pool_list:
                    if (t ^ x) in pool_set and (t ^ x):
                        pool_list.append(t)
                        pool_set.add(t)
                        uncovered.discard(t)
                        order.append((t, x, t ^ x))
                        progress = True
                        break

    def derive(t, pool_list, pool_set):
        for x in pool_list:
            y = t ^ x
            if y and y in pool_set:
                return (x, y)
        return None

    def enabling(pool_list, pool_set, uncovered):
        out = {}
        for t in uncovered:
            for x in pool_list:
                u = t ^ x
                if u and u not in pool_set:
                    out[u] = out.get(u, 0) + 1
        return out

    def creatable(pool_list, pool_set):
        out = set()
        n = len(pool_list)
        for i in range(n):
            for j in range(i + 1, n):
                v = pool_list[i] ^ pool_list[j]
                if v and v not in pool_set:
                    out.add(v)
        return out

    def dfs(pool_list, pool_set, uncovered, order, h, memo):
        nodes[0] += 1
        if nodes[0] > node_cap:
            raise Budget
        close(pool_list, pool_set, uncovered, order)
        if not uncovered:
            return order
        if h == 0:
            return None
        key = frozenset(pool_set)
        if key in memo[h]:
            return None
        memo[h].add(key)
        enab = enabling(pool_list, pool_set, uncovered)
        if h == 1:
            cands = list(enab)
        else:
            cands = list(creatable(pool_list, pool_set))
        cands.sort(key=lambda u: (-enab.get(u, 0), bin(u).count("1"), u))
        for u in cands:
            d = derive(u, pool_list, pool_set)
            if d is None:
                continue
            res = dfs(pool_list + [u], pool_set | {u},
                      set(uncovered), order + [(u,) + d], h - 1, memo)
            if res is not None:
                return res
        return None

    for h in range(max_slack + 1):
        memo = [set() for _ in range(h + 1)]
        try:
            res = dfs(list(base), set(base), set(tset), [], h, memo)
        except Budget:
            return {"nt": nt, "h": None, "adds": nt + h, "chain": None,
                    "status": "budget", "nodes": nodes[0]}
        if res is not None:
            assert len(res) == nt + h
            return {"nt": nt, "h": h, "adds": nt + h, "chain": res,
                    "status": "exact", "nodes": nodes[0]}
    return {"nt": nt, "h": None, "adds": nt + max_slack + 1, "chain": None,
            "status": "open", "nodes": nodes[0]}


def verify_chain(targets, nbase, chain):
    """replay: every step XORs two earlier values; every weight>=2
    target appears among the chain values."""
    vals = {1 << i for i in range(nbase)}
    for (v, x, y) in chain:
        assert x in vals and y in vals and (x ^ y) == v and v not in vals
        vals.add(v)
    for t in targets:
        if bin(t).count("1") >= 2:
            assert t in vals, f"target not covered: {t:b}"
    return True


# ---- exhaustive reference (tiny cases only): direct XOR-SLP minimum ----
def brute_direct(wrows, nin, cap=8):
    """true min #XORs computing every row of W (masks over nin inputs),
    by IDDFS over all chains.  Exponential — selftest sizes only."""
    goal = {w for w in wrows if bin(w).count("1") >= 2}
    start = frozenset(1 << i for i in range(nin))

    def dfs(vals, k):
        if goal <= vals:
            return 0
        if k == 0:
            return None
        vl = sorted(vals)
        for i in range(len(vl)):
            for j in range(i + 1, len(vl)):
                v = vl[i] ^ vl[j]
                if v and v not in vals:
                    r = dfs(vals | {v}, k - 1)
                    if r is not None:
                        return r + 1
        return None

    for k in range(cap + 1):
        r = dfs(start, k)
        if r is not None:
            return k
    return None


def gf2_transposed(wrows, nin, nout):
    """A(W) via the GF(2) transposition principle:
    gf2_min_cover(rows of W^T) + (nin - nout)."""
    wt = [sum(((wrows[o] >> i) & 1) << o for o in range(nout))
          for i in range(nin)]
    res = gf2_min_cover(wt, nout)
    assert res["status"] == "exact"
    return res["adds"] + (nin - nout)


# ---- the scheme-level wrapper ----
def gamma_masks(bits, dims=DIMS):
    """the r rows of W^T = per-product gamma support vectors (9-bit)."""
    n1, n2, n3, r = dims
    nv = len(bits)
    signs = {v: 1 for v in range(nv)}          # support only
    _, _, cforms = scheme_forms(bits, signs, dims)
    rows = c_transpose_rows(cforms, r)
    return [sum((1 if c else 0) << i for i, c in enumerate(row))
            for row in rows]


def c_gf2_exact(bits, dims=DIMS, max_slack=6, node_cap=20_000_000):
    """exact GF(2) C-side adds (model-independent Z lower bound).
    Returns (adds_or_None, res); on non-exact, res['adds']+r-9 is a LB."""
    n1, n2, n3, r = dims
    res = gf2_min_cover(gamma_masks(bits, dims), n1 * n3,
                        max_slack, node_cap)
    if res["status"] != "exact":
        return None, res
    return res["adds"] + (r - n1 * n3), res


def load_bits(path):
    return [int(c) for c in open(path).read().split()[-1].strip()]


def selftest():
    import random
    # 1. hand cases: cover + transposition constant vs exhaustive direct
    cases = [
        ([0b011, 0b110], 3),          # 2 outs over 3 ins
        ([0b111, 0b111], 3),          # duplicate rows
        ([0b01, 0b10], 2),            # identity: 0 adds
        ([0b1111, 0b0111, 0b0011], 4),
    ]
    for wrows, nin in cases:
        direct = brute_direct(wrows, nin)
        trans = gf2_transposed(wrows, nin, len(wrows))
        assert direct == trans, (wrows, nin, direct, trans)
    # 2. random tiny matrices, no zero rows/cols: direct == transposed
    rng = random.Random(11)
    done = 0
    while done < 60:
        nin, nout = rng.choice([(3, 3), (4, 3), (4, 4), (5, 3)])
        wrows = [rng.randrange(1, 1 << nin) for _ in range(nout)]
        if any(not any((w >> i) & 1 for w in wrows) for i in range(nin)):
            continue                   # zero column
        direct = brute_direct(wrows, nin)
        if direct is None:
            continue
        trans = gf2_transposed(wrows, nin, nout)
        assert direct == trans, (wrows, nin, direct, trans)
        done += 1
    # 3. chain replay on a real cover
    tg = [0b101101, 0b011011, 0b110110, 0b111111]
    res = gf2_min_cover(tg, 6)
    assert res["status"] == "exact" and verify_chain(tg, 6, res["chain"])
    # 4. anchors: GF2 C is a lower bound <= the known Z-exact C
    import os
    here = __file__.rsplit("/", 1)[0]
    for name, zc in (("external/i19-perminov56.bits", 28),
                     ("perminov_cache/bits/sun56.bits", 30)):
        p = f"{here}/{name}"
        if not os.path.exists(p):
            print(f"  (skip anchor {name} — not present)")
            continue
        c, res = c_gf2_exact(load_bits(p))
        assert c is not None and c <= zc, (name, c, zc)
        print(f"  anchor {name}: C_GF2 = {c} (Z-exact {zc}) nt={res['nt']} h={res['h']}")
    print("selftest OK: transposition constant (4 hand + 60 random tiny "
          "cases vs exhaustive), chain replay, anchors")


def sweep(listfile, cutoff):
    paths = [l.strip() for l in open(listfile) if l.strip()]
    nonexact = 0
    lo = (10 ** 9, None)
    hits = 0
    for n, p in enumerate(paths, 1):
        m = re.search(r"-s(\d+)-", p)
        assert m, f"no -sNN- sides tag in {p}"
        s = int(m.group(1))
        c, res = c_gf2_exact(load_bits(p))
        if c is None:
            nonexact += 1
            c = res["adds"] + 14        # lower bound still usable
            tag = "LB"
        else:
            tag = "=="
        lb = s + c
        if lb < lo[0]:
            lo = (lb, p)
        if lb <= cutoff:
            hits += 1
            print(f"CAND {lb} {tag} {s}+{c}  {p}", flush=True)
    print(f"swept {len(paths)} reps; min GF2 bound {lo[0]} ({lo[1]}); "
          f"{hits} candidates <= {cutoff}; {nonexact} non-exact")


if __name__ == "__main__":
    if sys.argv[1:2] == ["selftest"]:
        selftest()
    elif sys.argv[1:2] == ["sweep"]:
        cutoff = 54
        argv = sys.argv[2:]
        if "--cutoff" in argv:
            i = argv.index("--cutoff")
            cutoff = int(argv[i + 1])
            del argv[i:i + 2]
        sweep(argv[0], cutoff)
    else:
        print(__doc__)
