#!/usr/bin/env python3
"""Finisher: exact analysis of r=22 near-miss assignments.

For each saved near-miss (594-bit assignment with 1-2 violated Brent
equations):
  1. identify the violated equation(s) — indices (a,b,c,d,p,q), type
     (delta / non-delta), and how over/under-covered;
  2. exhaustive small-radius repair:
       - all 1-flips (must fail or the solver would have finished),
       - all 2-flips with >=1 flip among the violated equation's vars,
       - 3-flips restricted to the violated equation's vars, plus
         2-in-eq x 1-anywhere;
     any success = an r=22 scheme (verified + saved + banner);
  3. per-tensor GF(2) closure diagnostics: for each of alpha/beta/gamma,
     solve the 9 exact linear group-systems given the other two tensors;
     report contradiction counts (0 anywhere = solvable = scheme).

Usage: python3 finisher22.py nearmiss/*.bits
"""
import itertools
import random
import sys

from brent import brent_equations, var_counts, verify_bits
from sls import Sls

N, R = 3, 22
NA, NB, NG = var_counts(N, N, N, R)
NV = NA + NB + NG
EQS = brent_equations(N, N, N, R)


def eq_meta(e):
    """equation index -> (a,b,c,d,p,q)."""
    # generation order in brent_equations: a,b,c,d,p,q nested (n=3 each)
    idx = []
    x = e
    for _ in range(6):
        idx.append(x % 3)
        x //= 3
    q, p, d, c, b, a = idx
    return a, b, c, d, p, q


def violated(bits):
    out = []
    for e, (mons, rhs) in enumerate(EQS):
        acc = 0
        for va, vb, vg in mons:
            acc ^= bits[va] & bits[vb] & bits[vg]
        if acc != rhs:
            out.append(e)
    return out


def eq_vars(e):
    vs = set()
    for mon in EQS[e][0]:
        vs.update(mon)
    return sorted(vs)


def make_prober(bits):
    """incremental flip-prober around a fixed assignment (Sls machinery:
    each flip touches only the ~78 incident equations)."""
    s = Sls(N, N, N, R, random.Random(0))
    s.bits = list(bits)
    s._recompute()

    def try_flips(flips):
        for v in flips:
            s.flip(v)
        ok = not s.unsat
        for v in reversed(flips):
            s.flip(v)
        return ok

    return try_flips


def closure_contradictions(bits):
    """per tensor: total contradiction rows over its 9 exact group solves."""
    res = {}
    for tensor in ("alpha", "beta", "gamma"):
        total = 0
        for gi in range(3):
            for gj in range(3):
                rows = []
                for a in range(3):
                    for b in range(3):
                        for c in range(3):
                            for d in range(3):
                                if tensor == "gamma":
                                    p, q = gi, gj
                                    coefs = [
                                        bits[m * 9 + a * 3 + b]
                                        & bits[NA + m * 9 + c * 3 + d]
                                        for m in range(R)]
                                    rhs = int(b == c and a == p and d == q)
                                elif tensor == "alpha":
                                    aa, bb = gi, gj
                                    p, q = a, b  # reuse loop vars as (p,q)
                                    coefs = [
                                        bits[NA + m * 9 + c * 3 + d]
                                        & bits[NA + NB + m * 9 + p * 3 + q]
                                        for m in range(R)]
                                    rhs = int(bb == c and aa == p and d == q)
                                else:
                                    cc, dd = gi, gj
                                    p, q = c, d  # reuse loop vars as (p,q)
                                    coefs = [
                                        bits[m * 9 + a * 3 + b]
                                        & bits[NA + NB + m * 9 + p * 3 + q]
                                        for m in range(R)]
                                    rhs = int(b == cc and a == p and dd == q)
                                row = 0
                                for m in range(R):
                                    if coefs[m]:
                                        row |= 1 << m
                                rows.append(row | (rhs << 63))
                # rref
                piv = {}
                contra = 0
                for row in rows:
                    for col, pr in piv.items():
                        if (row >> col) & 1:
                            row ^= pr
                    if row == 1 << 63:
                        contra += 1
                    elif row and row != 1 << 63:
                        c0 = min(i for i in range(R) if (row >> i) & 1) \
                            if row & ((1 << R) - 1) else None
                        if c0 is None:
                            contra += 1
                        else:
                            piv[c0] = row
                total += contra
        res[tensor] = total
    return res


def analyze(path):
    s = open(path).read().split()[-1].strip()
    bits = [int(c) for c in s]
    assert len(bits) == NV
    bad = violated(bits)
    print(f"\n=== {path.split('/')[-1]}: {len(bad)} violated ===")
    for e in bad:
        a, b, c, d, p, q = eq_meta(e)
        typ = "DELTA(type-3)" if EQS[e][1] == 1 else "non-delta"
        cover = sum(bits[va] & bits[vb] & bits[vg]
                    for va, vb, vg in EQS[e][0])
        print(f"  eq {e}: A[{a}{b}]*B[{c}{d}]->C[{p}{q}] {typ}, "
              f"rhs={EQS[e][1]}, covered {cover}x")
    if len(bad) > 2:
        print("  (skipping repair: too many violations)")
        return None

    evs = sorted(set(v for e in bad for v in eq_vars(e)))
    print(f"  violated-eq var set: {len(evs)} vars")
    try_flips = make_prober(bits)

    # radius 1
    for v in range(NV):
        if try_flips([v]):
            return [v]
    print("  radius-1: no repair (expected)")
    # radius 2: >=1 flip in evs
    for v in evs:
        for w in range(NV):
            if w != v and try_flips([v, w]):
                return [v, w]
    print(f"  radius-2 (>=1 in eq vars): no repair "
          f"({len(evs) * NV} pairs)")
    # radius 3: all-in-evs + 2-in-evs x 1-anywhere
    for tri in itertools.combinations(evs, 3):
        if try_flips(list(tri)):
            return list(tri)
    print(f"  radius-3 (all in eq vars): no repair "
          f"(C({len(evs)},3) triples)")
    n2 = 0
    for v, w in itertools.combinations(evs, 2):
        for u in range(NV):
            if u != v and u != w and try_flips([v, w, u]):
                return [v, w, u]
            n2 += 1
    print(f"  radius-3 (2 in eq vars x 1 anywhere): no repair ({n2} tried)",
          flush=True)

    cc = closure_contradictions(bits)
    print(f"  closure contradictions per tensor: {cc}")
    return None


def main():
    sols = []
    for path in sys.argv[1:]:
        fix = analyze(path)
        if fix:
            s = open(path).read().split()[-1].strip()
            bits = [int(c) for c in s]
            for v in fix:
                bits[v] ^= 1
            assert verify_bits(bits, N, N, N, R) == 0
            out = path.replace(".bits", ".SOLVED22.bits")
            open(out, "w").write("".join(map(str, bits)) + "\n")
            print("!" * 60)
            print(f"R22 SCHEME by {len(fix)}-flip repair -> {out}")
            print("!" * 60)
            sols.append(out)
    print(f"\n{len(sols)} repairs found over {len(sys.argv) - 1} near-misses")


if __name__ == "__main__":
    main()
