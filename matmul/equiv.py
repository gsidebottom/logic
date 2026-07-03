#!/usr/bin/env python3
"""de Groote equivalence for 3x3 mod-2 matrix-multiplication schemes.

Representation: each scheme is a multiset of 23 summands (A, B, C~) of
3x3 GF(2) matrices, where A = alpha block, B = beta block, and
C~ = gamma-TRANSPOSED (in this representation our convention coincides
with the HKS/JSC one, and the symmetry group acts as the clean cyclic
sandwich):

    (P,Q,R) in GL(3,2)^3:  (A,B,C~) -> (P A Q^-1, Q B R^-1, R C~ P^-1)
    swap  (transpose):     (A,B,C~) -> (B^T, A^T, C~^T)
    cycle:                 (A,B,C~) -> (B, C~, A)

Every matching constraint "g maps summand s to summand t" is LINEAR in
the 27 unknown bits of (P,Q,R):
    A_t Q = P A_s,   B_t R = Q B_s,   C~_t P = R C~_s
so exact equivalence = backtracking over summand matchings (pruned by
rank triples) + GF(2) nullspace enumeration + invertibility + a full
multiset check.  Invariant fingerprints (rank statistics of summands and
summand pair-sums) prune almost everything first.

CLI:
  python3 equiv.py selftest
  python3 equiv.py classes file.bits ... (or a file of `b <bits>` lines)
"""
import random
import sys

from brent import var_counts, verify_bits

NA, NB, _ = var_counts(3, 3, 3, 23)
R23 = 23

# ---- 3x3 GF(2) matrices as 9-bit ints, bit (3*i + j) = entry (i,j) ----


def mat_get(m, i, j):
    return (m >> (3 * i + j)) & 1


def mat_transpose(m):
    t = 0
    for i in range(3):
        for j in range(3):
            if mat_get(m, i, j):
                t |= 1 << (3 * j + i)
    return t


def mat_mul(a, b):
    c = 0
    for i in range(3):
        for j in range(3):
            v = 0
            for k in range(3):
                v ^= mat_get(a, i, k) & mat_get(b, k, j)
            if v:
                c |= 1 << (3 * i + j)
    return c


def mat_rank(m):
    rows = [(m >> (3 * i)) & 7 for i in range(3)]
    rank = 0
    for bit in (1, 2, 4):
        piv_idx = next((k for k in range(len(rows)) if rows[k] & bit), None)
        if piv_idx is None:
            continue
        piv = rows.pop(piv_idx)
        rows = [r ^ piv if r & bit else r for r in rows]
        rank += 1
    return rank


def mat_inv(m):
    """inverse over GF(2), or None."""
    a = [(m >> (3 * i)) & 7 for i in range(3)]
    b = [1, 2, 4]  # identity rows (column j lives at bit j)
    for col, bit in enumerate((1, 2, 4)):
        piv = next((k for k in range(col, 3) if a[k] & bit), None)
        if piv is None:
            return None
        a[col], a[piv] = a[piv], a[col]
        b[col], b[piv] = b[piv], b[col]
        for k in range(3):
            if k != col and a[k] & bit:
                a[k] ^= a[col]
                b[k] ^= b[col]
    inv = 0
    for i in range(3):
        inv |= b[i] << (3 * i)
    return inv


def rand_gl(rng):
    while True:
        m = rng.randrange(512)
        if mat_rank(m) == 3:
            return m


# ---- scheme <-> summands ----


def bits_to_summands(bits):
    """621-bit brent-order vector -> list of (A, B, C~) 9-bit ints."""
    out = []
    for m in range(R23):
        a = b = g = 0
        for k in range(9):
            if bits[m * 9 + k]:
                a |= 1 << k
            if bits[NA + m * 9 + k]:
                b |= 1 << k
            if bits[NA + NB + m * 9 + k]:
                g |= 1 << k
        out.append((a, b, mat_transpose(g)))
    return out


def summands_to_bits(summands):
    bits = [0] * 621
    for m, (a, b, ct) in enumerate(summands):
        g = mat_transpose(ct)
        for k in range(9):
            bits[m * 9 + k] = (a >> k) & 1
            bits[NA + m * 9 + k] = (b >> k) & 1
            bits[NA + NB + m * 9 + k] = (g >> k) & 1
    return bits


def apply_glw(summands, p, q, r):
    qi, ri, pi = mat_inv(q), mat_inv(r), mat_inv(p)
    assert qi is not None and ri is not None and pi is not None
    return [(mat_mul(mat_mul(p, a), qi), mat_mul(mat_mul(q, b), ri),
             mat_mul(mat_mul(r, c), pi)) for (a, b, c) in summands]


def s3_variants(summands):
    """the 6 slot-maps of the S3 action (identity, cycle, cycle^2, swap,
    swap*cycle, swap*cycle^2)."""
    def cyc(ss):
        return [(b, c, a) for (a, b, c) in ss]

    def swp(ss):
        return [(mat_transpose(b), mat_transpose(a), mat_transpose(c))
                for (a, b, c) in ss]

    v = [summands]
    v.append(cyc(v[-1]))
    v.append(cyc(v[-1]))
    v.append(swp(summands))
    v.append(cyc(v[-1]))
    v.append(cyc(v[-1]))
    return v


# ---- invariants ----


def fingerprint(summands):
    triples = sorted(
        tuple(sorted((mat_rank(a), mat_rank(b), mat_rank(c))))
        for (a, b, c) in summands)
    pair = {}
    n = len(summands)
    for i in range(n):
        ai, bi, ci = summands[i]
        for j in range(i + 1, n):
            aj, bj, cj = summands[j]
            t = tuple(sorted((mat_rank(ai ^ aj), mat_rank(bi ^ bj),
                              mat_rank(ci ^ cj))))
            pair[t] = pair.get(t, 0) + 1
    return (tuple(triples), tuple(sorted(pair.items())))


# ---- exact equivalence ----


def _rows_for_match(s, t):
    """27 GF(2) rows over 27 unknowns [P(9) | Q(9) | R(9)] for
    A_t Q = P A_s ; B_t R = Q B_s ; C_t P = R C_s."""
    (a_s, b_s, c_s), (a_t, b_t, c_t) = s, t
    rows = []
    # X_t Y = Z X_s: entry (i,j): sum_k X_t[i,k] Y[k,j] + sum_k Z[i,k] X_s[k,j]
    for (xt, xs, yoff, zoff) in (
        (a_t, a_s, 9, 0),    # A: Y=Q(+9), Z=P(+0)
        (b_t, b_s, 18, 9),   # B: Y=R(+18), Z=Q(+9)
        (c_t, c_s, 0, 18),   # C: Y=P(+0), Z=R(+18)
    ):
        for i in range(3):
            for j in range(3):
                row = 0
                for k in range(3):
                    if mat_get(xt, i, k):
                        row ^= 1 << (yoff + 3 * k + j)
                    if mat_get(xs, k, j):
                        row ^= 1 << (zoff + 3 * i + k)
                rows.append(row)
    return rows


class LinSys:
    """incremental RREF over GF(2), 27 homogeneous columns."""

    def __init__(self):
        self.piv = {}  # col -> row

    def clone(self):
        c = LinSys()
        c.piv = dict(self.piv)
        return c

    def add(self, row):
        for col, prow in self.piv.items():
            if (row >> col) & 1:
                row ^= prow
        if row == 0:
            return True
        col = row.bit_length() - 1
        for c2, pr in list(self.piv.items()):
            if (pr >> col) & 1:
                self.piv[c2] = pr ^ row
        self.piv[col] = row
        return True

    def nullspace_dim(self):
        return 27 - len(self.piv)

    def solutions(self, cap=256):
        """enumerate nonzero solutions (27-bit ints), up to cap."""
        free = [c for c in range(27) if c not in self.piv]
        if 2 ** len(free) > cap:
            return None
        sols = []
        for mask in range(1, 2 ** len(free)):
            x = 0
            for bi, c in enumerate(free):
                if (mask >> bi) & 1:
                    x |= 1 << c
            for col, prow in self.piv.items():
                v = bin(prow & x).count("1") & 1
                if v:
                    x |= 1 << col
            sols.append(x)
        return sols


def _try_solutions(sys_, s_summands, t_summands):
    sols = sys_.solutions()
    if sols is None:
        return None  # too many; caller should match more summands
    t_sorted = sorted(t_summands)
    for x in sols:
        p = x & 511
        q = (x >> 9) & 511
        r = (x >> 18) & 511
        if mat_rank(p) == 3 and mat_rank(q) == 3 and mat_rank(r) == 3:
            mapped = apply_glw(s_summands, p, q, r)
            if sorted(mapped) == t_sorted:
                return (p, q, r)
    return False


def equivalent(sa, sb, max_depth=4):
    """exact de Groote equivalence of two summand lists (23 each)."""
    fb = fingerprint(sb)
    for variant in s3_variants(sa):
        if fingerprint(variant) != fb:
            continue
        # buckets of sb by (unsorted) rank triple
        buck = {}
        for t in sb:
            buck.setdefault(
                (mat_rank(t[0]), mat_rank(t[1]), mat_rank(t[2])),
                []).append(t)
        # order variant summands by bucket rarity
        order = sorted(
            variant,
            key=lambda s: len(buck.get(
                (mat_rank(s[0]), mat_rank(s[1]), mat_rank(s[2])), [])))

        def bt(depth, sys_):
            if depth >= max_depth or sys_.nullspace_dim() <= 8:
                res = _try_solutions(sys_, variant, sb)
                if res:
                    return res
                if res is False and depth >= max_depth:
                    return False
                if res is None and depth >= len(order):
                    return False
            if depth >= len(order):
                return False
            s = order[depth]
            key = (mat_rank(s[0]), mat_rank(s[1]), mat_rank(s[2]))
            for t in buck.get(key, []):
                s2 = sys_.clone()
                for row in _rows_for_match(s, t):
                    s2.add(row)
                if s2.nullspace_dim() == 0:
                    continue  # only zero solution -> dead
                res = bt(depth + 1, s2)
                if res:
                    return res
            return False

        res = bt(0, LinSys())
        if res:
            return res
    return False


# ---- CLI ----


def load_schemes(paths):
    out = []
    for p in paths:
        for line in open(p):
            line = line.strip()
            if line.startswith("b "):
                line = line[2:]
            if len(line) == 621 and set(line) <= {"0", "1"}:
                bits = [int(c) for c in line]
                assert verify_bits(bits, 3, 3, 3, 23) == 0, \
                    f"{p} does not verify"
                out.append((p, bits_to_summands(bits)))
    return out


def selftest():
    rng = random.Random(1)
    from brent import laderman, scheme_to_bits
    lb = scheme_to_bits(*laderman(), 3, 3, 3, 23)
    lad = bits_to_summands(lb)
    # representation round-trip + group action preserves validity
    assert verify_bits(summands_to_bits(lad), 3, 3, 3, 23) == 0
    for trial in range(12):
        p, q, r = rand_gl(rng), rand_gl(rng), rand_gl(rng)
        img = apply_glw(lad, p, q, r)
        rng.shuffle(img)
        for variant in (img, s3_variants(img)[rng.randrange(6)]):
            assert verify_bits(summands_to_bits(variant), 3, 3, 3, 23) == 0, \
                "group action must preserve the Brent equations"
        assert fingerprint(img) == fingerprint(lad)
        w = equivalent(lad, img)
        assert w, f"trial {trial}: image must be equivalent"
    print("group action + equivalence(image) OK (12 random elements)")
    smirnov = load_schemes(["seeds/smirnov.bits"])[0][1]
    assert fingerprint(smirnov) != fingerprint(lad)
    assert equivalent(lad, smirnov) is False
    print("laderman vs smirnov: inequivalent (fingerprint + exact) OK")


def classes(paths):
    schemes = load_schemes(paths)
    print(f"{len(schemes)} verified schemes")
    by_fp = {}
    for name, s in schemes:
        by_fp.setdefault(fingerprint(s), []).append((name, s))
    print(f"{len(by_fp)} distinct fingerprints")
    ncls = 0
    for fp, members in sorted(by_fp.items(), key=lambda kv: -len(kv[1])):
        reps = []
        for name, s in members:
            hit = None
            for rname, rs in reps:
                if equivalent(s, rs):
                    hit = rname
                    break
            if hit is None:
                reps.append((name, s))
        ncls += len(reps)
        if len(members) > 1 or len(reps) > 1:
            print(f"  fp-group of {len(members)}: {len(reps)} exact "
                  f"class(es); reps: "
                  f"{', '.join(n.split('/')[-1] for n, _ in reps[:4])}"
                  f"{'...' if len(reps) > 4 else ''}")
    print(f"TOTAL de-Groote classes: {ncls}")


if __name__ == "__main__":
    if sys.argv[1] == "selftest":
        selftest()
    elif sys.argv[1] == "classes":
        classes(sys.argv[2:])
    else:
        sys.exit("usage: equiv.py selftest | classes file...")
