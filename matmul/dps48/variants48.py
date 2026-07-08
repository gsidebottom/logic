#!/usr/bin/env python3
"""Build the S3 slot-variant portfolio of a rational <4x4x4:48> LRP
triple over exact Fractions (no dyadic-coefficient assumption, unlike
cse48), Brent-check every candidate, normalize rows to primitive
integer form (per-product projective freedom), and export .sms triples
for a PLinOpt sweep.

Usage: variants48.py SRCDIR OUTDIR      # SRCDIR holds L.sms R.sms P.sms
"""
import os
import sys
from fractions import Fraction


def parse_sms(path):
    rows = cols = None
    m = None
    for ln in open(path):
        ln = ln.strip()
        if not ln or ln.startswith("#"):
            continue
        p = ln.split()
        if rows is None:
            rows, cols = int(p[0]), int(p[1])
            m = [[Fraction(0)] * cols for _ in range(rows)]
            continue
        i, j = int(p[0]), int(p[1])
        if i == 0 and j == 0:
            break
        m[i - 1][j - 1] = Fraction(p[2])
    return m


def t16(mat):
    """reindex the 16-dim axis by the 4x4 transpose (p,q)->(q,p)."""
    out = []
    for row in mat:
        r = [Fraction(0)] * 16
        for j, v in enumerate(row):
            p, q = divmod(j, 4)
            r[4 * q + p] = v
        out.append(r)
    return out


def transpose(m):
    return [list(c) for c in zip(*m)]


def brent_ok(s1, s2, out):
    """all 4096 Brent equations over Q (C row-major)."""
    for x in range(16):
        a, b = divmod(x, 4)
        for y in range(16):
            c, d = divmod(y, 4)
            for z in range(16):
                p, q = divmod(z, 4)
                s = sum(s1[i][x] * s2[i][y] * out[z][i] for i in range(48))
                if s != (1 if (b == c and a == p and d == q) else 0):
                    return False
    return True


def primitive_gauge(s1, s2, out):
    """per product: scale each side row to primitive integers (clear
    denominators, divide by content), compensating in out's column."""
    from math import gcd
    for i in range(48):
        for side in (s1, s2):
            row = side[i]
            den = 1
            for v in row:
                den = den * v.denominator // gcd(den, v.denominator)
            num = 0
            for v in row:
                num = gcd(num, abs(v.numerator * (den // v.denominator)))
            if num == 0:
                continue
            scale = Fraction(den, num)      # row * scale is primitive
            if scale != 1:
                side[i] = [v * scale for v in row]
                for zrow in out:
                    zrow[i] = zrow[i] / scale
    return s1, s2, out


def column_gauge(s1, s2, out):
    """mode-2-style shift rebalancing over general rationals: per
    product column of `out`, factor out the modal power of two
    (denominators only move by 2^k; odd mantissas like 3 stay), pushing
    the scale onto side-1's row — one hoisted shift there vs many in
    the out column."""
    from collections import Counter
    for i in range(48):
        exps = []
        for z in range(16):
            v = out[z][i]
            if v:
                # 2-adic valuation of v
                num, den = v.numerator, v.denominator
                e = 0
                while num % 2 == 0:
                    num //= 2
                    e += 1
                while den % 2 == 0:
                    den //= 2
                    e -= 1
                exps.append(e)
        if not exps:
            continue
        mode, cnt = Counter(exps).most_common(1)[0]
        # rescale only when it strictly reduces distinct nonzero
        # exponents (same cost() logic as cse48's gauge mode 2)
        def ndist(k):
            return len({e - k for e in exps if e - k != 0}) + (k != 0)
        best = min(sorted({0, *exps}, key=lambda k: (k != 0)), key=ndist)
        if best:
            sc = Fraction(2) ** best
            for z in range(16):
                out[z][i] = out[z][i] / sc
            s1[i] = [v * sc for v in s1[i]]
    return s1, s2, out


def write_sms(path, mat):
    rows, cols = len(mat), len(mat[0])
    with open(path, "w") as f:
        f.write(f"{rows} {cols} R\n")
        for i, row in enumerate(mat):
            for j, v in enumerate(row):
                if v:
                    f.write(f"{i + 1} {j + 1} {v}\n")
        f.write("0 0 0\n")


def main():
    src, outdir = sys.argv[1], sys.argv[2]
    os.makedirs(outdir, exist_ok=True)
    L = parse_sms(f"{src}/L.sms")           # 48 x 16
    R = parse_sms(f"{src}/R.sms")           # 48 x 16
    P = parse_sms(f"{src}/P.sms")           # 16 x 48
    fams = {"L": L, "R": R, "Pt": transpose(P)}
    names = list(fams)
    kept = 0
    for a in names:
        for b in names:
            for c in names:
                if len({a, b, c}) != 3:
                    continue
                for bits in range(8):
                    mk = lambda k, fl: t16(fams[k]) if fl else \
                        [row[:] for row in fams[k]]
                    s1 = mk(a, bits & 1)
                    s2 = mk(b, bits & 2)
                    ot = mk(c, bits & 4)             # 48 x 16
                    out = transpose(ot)              # 16 x 48
                    s1, s2, out = primitive_gauge(s1, s2, out)
                    gmode = ""
                    if os.environ.get("COLGAUGE"):
                        s1, s2, out = column_gauge(s1, s2, out)
                        gmode = "_g2"
                    if brent_ok(s1, s2, out):
                        tag = lambda f: "t" if f else ""
                        name = (f"{a}{tag(bits & 1)}_{b}{tag(bits & 2)}"
                                f"_{c}{tag(bits & 4)}{gmode}")
                        write_sms(f"{outdir}/{name}_L.sms", s1)
                        write_sms(f"{outdir}/{name}_R.sms", s2)
                        write_sms(f"{outdir}/{name}_P.sms", out)
                        kept += 1
                        print(f"  {name}: Brent OK")
    print(f"{kept} variants written to {outdir}")


if __name__ == "__main__":
    main()
