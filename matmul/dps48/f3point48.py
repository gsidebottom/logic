#!/usr/bin/env python3
"""Mod-3 lower bounds on the additions of any Z[1/2] program for a rank-48
4x4 scheme AT ITS GIVEN REPRESENTATIVE (no orbit scan: GL(4,3) has 63,180
monomial cosets per factor, far beyond a table scan).  Per side: distinct
non-unit targets up to sign in F_3^16, the closure test, and a one-helper
exactness test; the output side counts transposed, +32.  Scalings are free
over F_3, so this bounds additions only.

Usage: f3point48.py PREFIX L_ADDS R_ADDS P_OPS   (PREFIX_{L,R,P}.sms; counts from SLPchecker)
2026-10-20 on PLinOpt's 4x4x4_48_202 (L 54+2, R 54+2, P 90): bounds L >= 42,
R >= 42, Pt >= 40 (+32) -> 156 vs 198 additions; the 204: 40/40/40 -> 152 vs 200.
Each side sits 12-18 additions above its cheap floor, so closure-level
bounds cannot decide whether these programs have slack; that needs search.
"""
from fractions import Fraction as Fr
import itertools, sys, time
W = 16; MASK = (1 << W) - 1
def sms(path):
    M = None
    for ln in open(path):
        p = ln.split()
        if M is None:
            if len(p) >= 2 and p[0].isdigit() and p[1].isdigit():
                M = [[Fr(0)] * int(p[1]) for _ in range(int(p[0]))]
            continue
        if len(p) < 3 or (p[0] == "0" and p[1] == "0"): break
        M[int(p[0]) - 1][int(p[1]) - 1] = Fr(p[2])
    return M
def mod3(x):
    assert x.denominator % 3, x
    return (x.numerator * pow(x.denominator, -1, 3)) % 3
def key_of(vec):
    ones = sum(1 << k for k, d in enumerate(vec) if d == 1); twos = sum(1 << k for k, d in enumerate(vec) if d == 2)
    nz = ones | twos
    if nz == 0 or (nz & (nz - 1)) == 0: return -1
    if twos & (nz & -nz): ones, twos = twos, ones
    return ones | (twos << W)
def add(x, y):
    x1, x2, y1, y2 = x & MASK, x >> W, y & MASK, y >> W
    s1 = (x1 & ~y1 & ~y2) | (y1 & ~x1 & ~x2) | (x2 & y2); s2 = (x2 & ~y1 & ~y2) | (y2 & ~x1 & ~x2) | (x1 & y1)
    return (s1 & MASK) | ((s2 & MASK) << W)
def neg(x): return (x >> W) | ((x & MASK) << W)
def norm(x):
    nz = (x & MASK) | (x >> W)
    return 0 if nz == 0 else (neg(x) if (x >> W) & (nz & -nz) else x)
def closure(targets, extra=()):
    have = set(1 << k for k in range(W)) | set(extra); rem = set(targets) - have
    grew = True
    while rem and grew:
        grew = False
        for u in list(rem):
            for a in have:
                if norm(add(u, neg(a))) in have or norm(add(u, a)) in have:
                    have.add(u); rem.discard(u); grew = True; break
    return have, rem
def side_bound(rows, label, prog_adds):
    keys = sorted({k for k in (key_of(v) for v in rows) if k >= 0}); t = len(keys)
    have, rem = closure(keys)
    if not rem:
        print(f"  {label}: {t} targets, closure reaches all -> bound {t}; program {prog_adds} (slack {prog_adds - t})"); return t
    cands = {h for a, b in itertools.combinations(sorted(have), 2) for h in (norm(add(a, b)), norm(add(a, neg(b)))) if h and h not in have}
    ok1 = any(not closure(keys, (h,))[1] for h in cands)
    lb = t + 1 if ok1 else t + 2
    print(f"  {label}: {t} targets, closure misses {len(rem)}, one helper {'suffices' if ok1 else 'does not suffice'} -> bound {'=' if ok1 else '>='} {lb}; program {prog_adds} additions (slack <= {prog_adds - lb})")
    return lb
pre, la, ra, po = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
L, R, P = sms(pre + "_L.sms"), sms(pre + "_R.sms"), sms(pre + "_P.sms")
n = len(L)
bl = side_bound([[mod3(x) for x in row] for row in L], "L ", la)
br = side_bound([[mod3(x) for x in row] for row in R], "R ", ra)
bp = side_bound([[mod3(P[i][k]) for i in range(16)] for k in range(n)], "Pt", po - (n - 16))
print(f"total additions >= {bl + br + bp + (n - 16)} vs program {la + ra + po}")
