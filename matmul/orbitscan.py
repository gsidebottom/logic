#!/usr/bin/env python3
"""Exhaustive de Groote orbit scan for low-addition representatives.

The sandwich action factors by side: A-forms depend only on (P,Q),
B-forms on (Q,R), C-forms on (R,P).  So the whole 168^3 orbit (per S3
variant) is covered by three 168x168 cost tables plus a min-plus scan —
no hill-climbing, no misses.

Side costs are computed over GF(2) (XOR chain covering, exact, via the
same closure+helper IDDFS as sidemin.py).  A GF(2) side cost is a LOWER
bound on the ternary/Z side cost of the same representative (reduce any
Z-chain mod 2), so
    floor_sides = min over (P,Q,R) of [A_gf2(P,Q) + B_gf2(Q,R)]
is a sound orbit-wide lower bound on Z input-side additions.  The C
table is a greedy GF(2) pair-CSE ESTIMATE (ranking only, no bound).
Candidates with A+B+C_est <= cutoff are re-scored exactly over Z
(lift models + sidemin + restart-greedy C) via orbit55.score.

Usage:
  python3 orbitscan.py scheme.bits [--variants 012345] [--cutoff 57]
      [--rescore-top 60] [--models 6] [--crestarts 200] [--outdir DIR]
"""
import sys
import time

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from brent import verify_bits
from equiv import (bits_to_summands, mat_inv, mat_mul, mat_rank,
                   s3_variants, summands_to_bits)
from orbit55 import score

GL = [m for m in range(512) if mat_rank(m) == 3]
GLI = {m: mat_inv(m) for m in GL}
NG = len(GL)  # 168


# ---------------- GF(2) exact side cost (9-bit int rows) ----------------

def gf2_min_side(rows, max_slack=3, node_cap=300_000):
    tset = set()
    for r in rows:
        if bin(r).count("1") >= 2:
            tset.add(r)
    nt = len(tset)
    if nt == 0:
        return 0
    nodes = [0]
    base = [1 << i for i in range(9)]

    def close(pool, uncovered):
        progress = True
        while progress:
            progress = False
            for t in list(uncovered):
                for x in pool:
                    if (t ^ x) in pool and (t ^ x) != x:
                        pool.add(t)
                        uncovered.discard(t)
                        progress = True
                        break
        return pool, uncovered

    def dfs(pool, uncovered, h, memo):
        nodes[0] += 1
        if nodes[0] > node_cap:
            raise RuntimeError("budget")
        close(pool, uncovered)
        if not uncovered:
            return True
        if h == 0:
            return False
        key = frozenset(pool)
        if key in memo[h]:
            return False
        memo[h].add(key)
        if h == 1:
            cands = {t ^ x for t in uncovered for x in pool} - pool - {0}
            cands = {u for u in cands
                     if any((u ^ x) in pool and (u ^ x) != x for x in pool)}
        else:
            cands = set()
            pl = list(pool)
            for i in range(len(pl)):
                for j in range(i):
                    v = pl[i] ^ pl[j]
                    if v and v not in pool:
                        cands.add(v)
        enab = {}
        for t in uncovered:
            for x in pool:
                u = t ^ x
                if u in cands:
                    enab[u] = enab.get(u, 0) + 1
        for u in sorted(cands, key=lambda u: (-enab.get(u, 0),
                                              bin(u).count("1"), u)):
            if dfs(set(pool) | {u}, set(uncovered), h - 1, memo):
                return True
        return False

    for h in range(max_slack + 1):
        memo = [set() for _ in range(h + 1)]
        if dfs(set(base), set(tset), h, memo):
            return nt + h
    return nt + max_slack + 1  # lower bound; flagged by caller if hit


# ------------- GF(2) greedy C estimate (9 forms over 23 products) -------

def gf2_c_greedy(forms):
    """forms: list of ints (bitmask over product vars).  Greedy pair
    extraction; returns adds (estimate, not a bound)."""
    forms = [f for f in forms]
    nxt = 64  # aux symbol bit index start (>= 23 products)
    adds = 0
    while True:
        counts = {}
        for f in forms:
            bs = []
            x = f
            while x:
                b = x & -x
                bs.append(b)
                x ^= b
            for i in range(len(bs)):
                for j in range(i):
                    counts[bs[i] | bs[j]] = counts.get(bs[i] | bs[j], 0) + 1
        pair = max(counts, key=counts.get, default=None)
        if pair is None or counts[pair] < 2:
            break
        w = 1 << nxt
        nxt += 1
        adds += 1
        forms = [(f ^ pair) | w if (f & pair) == pair else f for f in forms]
    adds += sum(max(bin(f).count("1") - 1, 0) for f in forms)
    return adds


# ---------------- tables + scan ----------------

def side_tables(summands, verbose=True):
    """A[pi,qi], B[qi,ri], C_est[ri,pi] (int16 numpy)."""
    amats = [s[0] for s in summands]
    bmats = [s[1] for s in summands]
    cmats = [s[2] for s in summands]  # C~ = gamma transposed, 9-bit
    A = np.zeros((NG, NG), dtype=np.int16)
    B = np.zeros((NG, NG), dtype=np.int16)
    C = np.zeros((NG, NG), dtype=np.int16)
    t0 = time.time()
    for li, L in enumerate(GL):
        LA = [mat_mul(L, m) for m in amats]
        LB = [mat_mul(L, m) for m in bmats]
        LC = [mat_mul(L, m) for m in cmats]
        for ri_, Rm in enumerate(GL):
            Ri = GLI[Rm]
            A[li, ri_] = gf2_min_side([mat_mul(m, Ri) for m in LA])
            B[li, ri_] = gf2_min_side([mat_mul(m, Ri) for m in LB])
            # C-side: 9 forms over 23 products; form j = {m: bit j set}
            rows = [mat_mul(m, Ri) for m in LC]
            forms = [0] * 9
            for m, g in enumerate(rows):
                for j in range(9):
                    if (g >> j) & 1:
                        forms[j] |= 1 << m
            C[li, ri_] = gf2_c_greedy(forms)
        if verbose and (li + 1) % 42 == 0:
            print(f"    tables {li+1}/{NG} rows  "
                  f"[{time.time()-t0:.0f}s]", flush=True)
    return A, B, C


def scan_variant(summands, cutoff):
    """returns floor_sides, best_est, candidates [(est, pi, qi, ri)]."""
    A, B, C = side_tables(summands)
    # floor over sides: min over q of  min_p A[p,q] + min_r B[q,r]
    floor_sides = int(min(A[:, q].min() + B[q, :].min() for q in range(NG)))
    best_est = 10 ** 9
    cands = []
    for q in range(NG):
        # tot[p, r] = A[p,q] + B[q,r] + C[r,p]
        tot = A[:, q][:, None] + B[q, :][None, :] + C.T
        m = int(tot.min())
        best_est = min(best_est, m)
        if m <= cutoff:
            ps, rs = np.where(tot <= cutoff)
            for p, r in zip(ps.tolist(), rs.tolist()):
                cands.append((int(tot[p, r]), p, q, r))
    cands.sort()
    return floor_sides, best_est, cands


def exhaust_sides(summands, vi, name, budget, models, crestarts, outdir):
    """enumerate ALL (P,Q,R) with exact GF2 sides A+B <= budget, dedupe
    the resulting schemes, Z-rescore each at high C effort.  This makes
    the side dimension exhaustive; C remains heuristic (upper bound)."""
    A, B, C = side_tables(summands)
    triples = []
    for q in range(NG):
        ps = np.where(A[:, q] + int(B[q, :].min()) <= budget)[0]
        if len(ps) == 0:
            continue
        for p in ps.tolist():
            rs = np.where(int(A[p, q]) + B[q, :] <= budget)[0]
            for r in rs.tolist():
                triples.append((int(A[p, q] + B[q, r]), p, q, r))
    triples.sort()
    print(f"   v{vi}: {len(triples)} triples with sides <= {budget}",
          flush=True)
    seen = {}
    best = (10 ** 9, None)
    for sd, p, q, r in triples:
        img = [(mat_mul(mat_mul(GL[p], a), GLI[GL[q]]),
                mat_mul(mat_mul(GL[q], b), GLI[GL[r]]),
                mat_mul(mat_mul(GL[r], c), GLI[GL[p]]))
               for (a, b, c) in summands]
        nb = summands_to_bits(img)
        key = "".join(map(str, nb))
        if key in seen:
            continue
        seen[key] = True
        assert verify_bits(nb, 3, 3, 3, 23) == 0
        tot, det = score(nb, models, crestarts, 4321 + sd,
                         full_verify=True)
        if tot < best[0]:
            best = (tot, det)
            a, b, c, mi = det if det else (0, 0, 0, 0)
            print(f"   v{vi} sides-exhaust NEW BEST Z {tot} = {a}+{b}+{c} "
                  f"(gf2-sides {sd}, P{p} Q{q} R{r}, m{mi})", flush=True)
            if outdir and tot <= 56:
                fn = f"{outdir}/{name}-v{vi}-x{tot}.bits"
                open(fn, "w").write(key + "\n")
            if tot <= 55:
                print(f"   *** JACKPOT {tot} <= 55 ***", flush=True)
    print(f"   v{vi} sides-exhaust done: {len(seen)} distinct schemes, "
          f"best Z {best[0]}", flush=True)
    return best


def main():
    argv = sys.argv[1:]

    def opt(name, default, cast=int):
        if name in argv:
            i = argv.index(name)
            v = cast(argv[i + 1])
            del argv[i:i + 2]
            return v
        return default

    variants = opt("--variants", "012345", str)
    cutoff = opt("--cutoff", 57)
    top = opt("--rescore-top", 60)
    models = opt("--models", 6)
    crestarts = opt("--crestarts", 200)
    outdir = opt("--outdir", None, str)
    xsides = opt("--exhaust-sides", None)
    path = argv[0]

    bits0 = [int(c) for c in open(path).read().split()[-1].strip()]
    assert verify_bits(bits0, 3, 3, 3, 23) == 0
    name = path.split("/")[-1].replace(".bits", "")
    vlist = s3_variants(bits_to_summands(bits0))

    global_best = (10 ** 9, None)
    for vi in [int(c) for c in variants]:
        sm = vlist[vi]
        if xsides is not None:
            print(f"== {name} variant {vi}: sides-exhaust "
                  f"budget {xsides}", flush=True)
            exhaust_sides(sm, vi, name, xsides, models, crestarts, outdir)
            continue
        print(f"== {name} variant {vi}: building GF(2) tables "
              f"(168x168 x3)...", flush=True)
        floor_sides, best_est, cands = scan_variant(sm, cutoff)
        print(f"   sides floor (GF2, orbit-wide) = {floor_sides}; "
              f"best est total = {best_est}; "
              f"candidates <= {cutoff}: {len(cands)}", flush=True)
        seen = set()
        for est, p, q, r in cands[: top * 5]:
            if len(seen) >= top:
                break
            img = [(mat_mul(mat_mul(GL[p], a), GLI[GL[q]]),
                    mat_mul(mat_mul(GL[q], b), GLI[GL[r]]),
                    mat_mul(mat_mul(GL[r], c), GLI[GL[p]]))
                   for (a, b, c) in sm]
            nb = summands_to_bits(img)
            key = "".join(map(str, nb))
            if key in seen:
                continue
            seen.add(key)
            assert verify_bits(nb, 3, 3, 3, 23) == 0
            tot, det = score(nb, models, crestarts, 1234 + est,
                             full_verify=True)
            if tot < global_best[0]:
                global_best = (tot, (vi, p, q, r, det, nb))
                a, b, c, mi = det
                print(f"   NEW BEST Z total {tot} = {a}+{b}+{c} "
                      f"(v{vi} P{p} Q{q} R{r} m{mi}, est {est})",
                      flush=True)
                if outdir and tot <= 56:
                    fn = f"{outdir}/{name}-v{vi}-{tot}.bits"
                    open(fn, "w").write(key + "\n")
                    print(f"   wrote {fn}", flush=True)
                if tot <= 55:
                    print(f"   *** JACKPOT {tot} <= 55 ***", flush=True)
    tot, info = global_best
    if info:
        vi, p, q, r, det, nb = info
        print(f"{name}: SCAN BEST Z = {tot} "
              f"(variant {vi}, {det})", flush=True)
    else:
        print(f"{name}: no candidate <= cutoff {cutoff}", flush=True)


if __name__ == "__main__":
    main()
