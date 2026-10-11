#!/usr/bin/env python3
"""Gauge sweep for the B-leg sign obstruction: diagonal +-1 sandwich
flips keep the class, the masks, and hence the F2 certificates, while
re-signing entries.  B-leg entry beta_{jk} (position 3j+k) flips by
q_j * r_k for sign vectors q, r in {+-1}^3 (p, the third diagonal,
does not touch the B leg).  For each of the 64 (q, r) gauges, try the
B certificates until one sign-lifts; report every working gauge.

A working (q, r) must then be checked jointly: A entries flip by
p_i q_j and C entries by r_k p_i, so p in {+-1}^3 is chosen afterwards
against the A/C certificates (A lifted 300/300 and C 168/300 under the
identity gauge, so the joint step has plenty of room).

Usage: fbgauge.py schemes.tgz certsB [max_certs_per_gauge]
"""
import itertools, sys, tarfile
from fractions import Fraction

TGZ, CERTB = sys.argv[1], sys.argv[2]
MAXC = int(sys.argv[3]) if len(sys.argv) > 3 else 300
SIDE = int(sys.argv[4]) if len(sys.argv) > 4 else 1  # 0=A 1=B 2=C
TAB = "schemes/18x2+51x+4y6+6y4+13y3+z32+z28+z27/i19w225c4efh-000.tab"

def parse_tab(text):
    out, cur = [], []
    for ln in text.splitlines():
        if "|" not in ln:
            continue
        parts = [p.split() for p in ln.split("|")]
        if len(parts) != 3 or any(len(g) != 3 for g in parts):
            continue
        cur.append([[int(v) for v in g] for g in parts])
        if len(cur) == 3:
            out.append(tuple(tuple(v for r in cur for v in r[s]) for s in range(3)))
            cur = []
    return out

def mask(row):
    return int("".join(str(v & 1) for v in row), 2)

def parse_certs(path):
    certs, basis, adds = [], None, []
    for ln in open(path):
        ln = ln.strip()
        if ln.startswith("basis:"):
            if basis:
                certs.append((basis, adds))
            basis = [int(m, 2) for m in ln.split()[1:]]
            adds = []
        elif ln.startswith("add "):
            x, _, y, _, s = ln.split()[1:6]
            adds.append((int(x, 2), int(y, 2), int(s, 2)))
    if basis:
        certs.append((basis, adds))
    return certs

def det_unimodular(rows):
    A = [[Fraction(v) for v in r] for r in rows]
    d = Fraction(1)
    n = len(rows)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return False
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            if A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return abs(d) == 1

def neg(v):
    return tuple(-x for x in v)

def add_vec(x, y, s):
    return tuple(a + s * b for a, b in zip(x, y))

def lift_leg(basis_masks, adds, rep_of_mask):
    base_reps = [rep_of_mask[m] for m in basis_masks]

    def dfs(i, forms):
        if i == len(adds):
            return True
        x, y, s = adds[i]
        for sign in (1, -1):
            val = add_vec(forms[x], forms[y], sign)
            if s in rep_of_mask:
                rep = rep_of_mask[s]
                if val != rep and val != neg(rep):
                    continue
            forms[s] = val
            if dfs(i + 1, forms):
                return True
            del forms[s]
        return False

    for eps in itertools.product((1, -1), repeat=8):
        eps = (1,) + eps
        rows = [r if e == 1 else neg(r) for e, r in zip(eps, base_reps)]
        if not det_unimodular(rows):
            continue
        if dfs(0, dict(zip(basis_masks, rows))):
            return True
    return False

sm = parse_tab(tarfile.open(TGZ, "r:gz").extractfile(TAB).read().decode())
assert len(sm) == 23
certs = parse_certs(CERTB)[:MAXC]
print(f"B certs: {len(certs)}; sweeping 64 (q,r) gauges", flush=True)

hits = []
for q in itertools.product((1, -1), repeat=3):
    for r in itertools.product((1, -1), repeat=3):
        rep = {}
        ok = True
        for a in sm:
            row = tuple(q[p // 3] * r[p % 3] * v for p, v in enumerate(a[SIDE]))
            m = mask(row)
            if m in rep:
                if rep[m] != row and rep[m] != neg(row):
                    ok = False
                    break
            else:
                rep[m] = row
        assert ok
        for ic, c in enumerate(certs):
            if lift_leg(*c, rep):
                hits.append((q, r, ic))
                print(f"GAUGE HIT q={q} r={r}: B cert {ic} lifts", flush=True)
                break
        else:
            print(f"q={q} r={r}: no lift in {len(certs)} certs", flush=True)

print(f"\n{len(hits)} of 64 gauges admit a B-leg lift")
