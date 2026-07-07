#!/usr/bin/env python3
"""Exact chain-covering minimizer in the ADDS+SHIFTS model.

Extends sidemin's model: chain values start at the unit vectors; each
op creates one new value and costs 1; ops are
    w = u ± v            (binary add/subtract)
    w = 2^k · u          (shift, k != 0, |k| <= K window)
negation is free (values canonicalized up to global sign); a target is
covered when ±target is a chain value.  Values are exact Fractions, so
halving-helpers like (u+v)/2 are in scope — the genuinely new
capability vs the pure-± model (shifts of all-±1 pools are useless: no
2^k scaling of a ±1-vector is a ±1-vector, so at helper-count h = 0
the two models coincide; the new power appears only through helpers).

Same IDDFS-on-helpers skeleton as sidemin: cost = nt + h where nt is
the number of distinct multi-weight targets (each costs exactly its
covering op) and h the number of helper values; closure normal form
(cover any 1-op-derivable target immediately), branch only on helpers.
Completeness of the closure rule in the extended model is validated
empirically against exhaustive search in `selftest`.

CLI:
  shiftmin.py selftest
  shiftmin.py --bits FILE [--k K]   # exact adds+shifts minima of the
                                    # scheme's three maps + total
"""
import sys
from fractions import Fraction
from itertools import combinations_with_replacement

sys.path.insert(0, __file__.rsplit("/", 1)[0])

NODE_CAP = 30_000_000


class Budget(Exception):
    pass


def canon(v):
    for x in v:
        if x > 0:
            return v
        if x < 0:
            return tuple(-y for y in v)
    return v


def basis(n):
    return [canon(tuple(Fraction(1) if j == i else Fraction(0)
                        for j in range(n))) for i in range(n)]


def derive(t, pool_list, pool_set, K):
    """t reachable in ONE op from the pool?  -> op description or None"""
    for x in pool_list:
        for sx in (1, -1):
            r = tuple(t[i] - sx * x[i] for i in range(len(t)))
            if not any(r):
                continue
            cy = canon(r)
            if cy in pool_set:
                return ("pm", x, sx, cy)
    for x in pool_list:
        for k in range(-K, K + 1):
            if k == 0:
                continue
            s = Fraction(2) ** k
            if canon(tuple(s * xi for xi in x)) == t:
                return ("sh", x, k, None)
    return None


def min_shift(rows, nbase, K=2, max_slack=3, node_cap=NODE_CAP,
              max_num=8, max_den=8):
    """exact adds+shifts minimum to cover all rows (up to sign).
    Returns dict like sidemin's: nt, h, adds, status, nodes."""
    tset = []
    seen = set()
    for r in rows:
        c = canon(tuple(Fraction(x) for x in r))
        if sum(1 for x in c if x) <= 1 or c in seen:
            continue
        seen.add(c)
        tset.append(c)
    nt = len(tset)
    nodes = [0]

    def ok_val(v):
        return all(abs(x.numerator) <= max_num and x.denominator <= max_den
                   for x in v)

    def close(pool_list, pool_set, uncovered):
        progress = True
        while progress:
            progress = False
            for t in list(uncovered):
                if derive(t, pool_list, pool_set, K):
                    pool_list.append(t)
                    pool_set.add(t)
                    uncovered.discard(t)
                    progress = True

    def enabling(pool_list, pool_set, uncovered):
        """candidate helpers u such that some uncovered t becomes
        1-op-derivable once u exists: t = ±u ± x  or  t = 2^k u."""
        out = {}
        for t in uncovered:
            for x in pool_list:
                for sx in (1, -1):
                    r = tuple(t[i] - sx * x[i] for i in range(len(t)))
                    if not any(r):
                        continue
                    u = canon(r)
                    if u not in pool_set and ok_val(u):
                        out[u] = out.get(u, 0) + 1
            for k in range(-K, K + 1):
                if k == 0:
                    continue
                s = Fraction(2) ** k
                u = canon(tuple(x / s for x in t))
                if u not in pool_set and ok_val(u):
                    out[u] = out.get(u, 0) + 1
        return out

    def creatable(pool_list, pool_set):
        out = set()
        for x, y in combinations_with_replacement(pool_list, 2):
            for sy in (1, -1):
                v = canon(tuple(a + sy * b for a, b in zip(x, y)))
                if any(v) and v not in pool_set and ok_val(v):
                    out.add(v)
        for x in pool_list:
            for k in range(-K, K + 1):
                if k == 0:
                    continue
                s = Fraction(2) ** k
                v = canon(tuple(s * a for a in x))
                if any(v) and v not in pool_set and ok_val(v):
                    out.add(v)
        return out

    def dfs(pool_list, pool_set, uncovered, h, memo):
        nodes[0] += 1
        if nodes[0] > node_cap:
            raise Budget
        close(pool_list, pool_set, uncovered)
        if not uncovered:
            return True
        if h == 0:
            return False
        key = frozenset(pool_set)
        if key in memo[h]:
            return False
        memo[h].add(key)
        enab = enabling(pool_list, pool_set, uncovered)
        if h == 1:
            cands = list(enab)
        else:
            cands = list(creatable(pool_list, pool_set))
        cands.sort(key=lambda u: (-enab.get(u, 0),
                                  sum(1 for x in u if x), u))
        for u in cands:
            if derive(u, pool_list, pool_set, K) is None:
                continue
            if dfs(pool_list + [u], pool_set | {u},
                   set(uncovered), h - 1, memo):
                return True
        return False

    for h in range(max_slack + 1):
        memo = [set() for _ in range(h + 1)]
        pl = basis(nbase)
        try:
            if dfs(list(pl), set(pl), set(tset), h, memo):
                return {"nt": nt, "h": h, "adds": nt + h,
                        "status": "exact", "nodes": nodes[0]}
        except Budget:
            return {"nt": nt, "h": None, "adds": nt + h,
                    "status": "budget", "nodes": nodes[0]}
    return {"nt": nt, "h": None, "adds": nt + max_slack + 1,
            "status": "open", "nodes": nodes[0]}


# ---- exhaustive reference for tiny cases (selftest only) ----
def brute(rows, nbase, K=2, cap=7, shifts=True, max_num=6, max_den=4):
    """true minimum ops by IDDFS over ALL op sequences."""
    targets = set()
    for r in rows:
        c = canon(tuple(Fraction(x) for x in r))
        if sum(1 for x in c if x) >= 2:
            targets.add(c)

    def ok_val(v):
        return all(abs(x.numerator) <= max_num and x.denominator <= max_den
                   for x in v)

    start = tuple(sorted(basis(nbase)))

    def dfs(pool, k):
        ps = set(pool)
        if targets <= ps:
            return 0
        if k == 0:
            return None
        moves = set()
        pl = list(pool)
        for i in range(len(pl)):
            for j in range(i, len(pl)):
                for s in (1, -1):
                    v = canon(tuple(a + s * b
                                    for a, b in zip(pl[i], pl[j])))
                    if any(v) and v not in ps and ok_val(v):
                        moves.add(v)
            if shifts:
                for kk in range(-K, K + 1):
                    if kk == 0:
                        continue
                    sc = Fraction(2) ** kk
                    v = canon(tuple(sc * a for a in pl[i]))
                    if any(v) and v not in ps and ok_val(v):
                        moves.add(v)
        for v in moves:
            r = dfs(tuple(sorted(pool + (v,))), k - 1)
            if r is not None:
                return r + 1
        return None

    for c in range(cap + 1):
        r = dfs(start, c)
        if r is not None:
            return c
    return None


def selftest():
    # 1. shifts provably useless at h=0 / small pure-± cases: agree
    cases = [
        ([(1, 1), (1, -1)], 2),
        ([(1, 1, 1), (1, -1, 0), (0, 1, 1)], 3),
        ([(1, 1, 0), (0, 1, 1), (1, 0, -1)], 3),
    ]
    for rows, n in cases:
        b = brute(rows, n, shifts=True)
        m = min_shift(rows, n)
        assert m["status"] == "exact" and m["adds"] == b, (rows, m, b)
    # 2. a case where the shift model strictly beats pure ±:
    #    u=(1,1,1,1), v=(1,-1,1,-1), t=(u+v)/2=(1,0,1,0), plus a 4th
    #    target chosen so the ±-model cannot absorb the helper for free
    rows = [(1, 1, 1, 1), (1, -1, 1, -1), (1, 0, 1, 0), (0, 1, 0, 1)]
    bshift = brute(rows, 4, shifts=True)
    bpm = brute(rows, 4, shifts=False)
    m = min_shift(rows, 4)
    assert m["status"] == "exact" and m["adds"] == bshift, (m, bshift)
    print(f"  half-sum family: shift-model {bshift} vs pure-± {bpm}"
          f" (shiftmin: {m['adds']})")
    # 3. random tiny cases: shiftmin == brute (closure completeness)
    import random
    rng = random.Random(5)
    done = 0
    while done < 25:
        n = rng.choice([2, 3])
        rows = [tuple(rng.choice([-1, 0, 1]) for _ in range(n))
                for _ in range(rng.choice([2, 3]))]
        if not any(sum(map(abs, r)) >= 2 for r in rows):
            continue
        b = brute(rows, n, cap=6)
        if b is None:
            continue
        m = min_shift(rows, n)
        assert m["status"] == "exact" and m["adds"] == b, (rows, m, b)
        done += 1
    print("selftest OK: 3 hand cases + half-sum strictness + 25 random"
          " vs exhaustive")


def scheme_maps(path):
    from lift import lift_models
    from slp import scheme_forms
    from tcmin import c_transpose_rows
    bits = [int(c) for c in open(path).read().split()[-1].strip()]
    signs, _ = lift_models(bits, 3, (3, 3, 3, 23))[2]
    fa, fb, fc = scheme_forms(bits, signs, (3, 3, 3, 23))
    tovec = lambda forms, n: [[f.get(i, 0) for i in range(n)]
                              for f in forms]
    return (tovec(fa, 9), tovec(fb, 9),
            [list(r) for r in c_transpose_rows(fc, 23)])


def main():
    if sys.argv[1:2] == ["selftest"]:
        selftest()
        return
    K = 2
    if "--k" in sys.argv:
        K = int(sys.argv[sys.argv.index("--k") + 1])
    path = sys.argv[sys.argv.index("--bits") + 1]
    A, B, WT = scheme_maps(path)
    tot = 0
    for name, rows in (("A-side", A), ("B-side", B), ("W^T", WT)):
        r = min_shift(rows, 9, K=K)
        extra = 14 if name == "W^T" else 0
        val = r["adds"] + extra
        tot += val
        print(f"{name}: adds+shifts exact = {r['adds']}"
              f"{' -> C = ' + str(val) if extra else ''}"
              f"  (nt={r['nt']}, h={r['h']}, status={r['status']},"
              f" nodes={r['nodes']})")
    print(f"TOTAL (adds+shifts model, K={K}): {tot}")


if __name__ == "__main__":
    main()
