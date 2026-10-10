#!/usr/bin/env python3
"""d-profile scan over the HKS rank-23 DB (schemes.tgz .tab files):
per class, the number of distinct factors on each side, and the
basis-change-model (Karstadt--Schwartz) addition floor they imply.

Per input leg, over ANY invertible basis change B: an SLP with a
additions creates at most a new linear forms beyond the 9 basis forms,
and d(U.B) = d(U) (invertible column action preserves row
distinctness), so  adds >= d(U) - 9.  The output leg, by the
transposition principle (adds(9x23 map) = adds(23x9 transpose) + 14),
floors at (d(W) - 9) + 14.  Hence, in every basis:

    per-step adds  >=  dA + dB + dC - 13.

d is counted mod 2 (the Nielsen/KS-over-F2-then-lift route: rows equal
mod 2 merge) and over Z up to row sign (negation-free +- model).

Validation gates (independent prior exact computations):
  - i19w225c4efh (our 55-add record class, Perminov cn122): exact flat
    sides are 13+14 => side d's must be {22, 23}; cfloor measured 22
    distinct gamma masks => dC = 22.  Expected floor2 = 54.
  - Nielsen's base class i12w195c23ci (arXiv 2609.06588): his in-basis
    sides are 12+12 => both side d's must be <= 21; his output 28 =>
    dC <= 23.

Usage: dprofile.py [path/to/schemes.tgz] [out.csv]
"""
import sys, tarfile, collections

TGZ = sys.argv[1] if len(sys.argv) > 1 else "dbcache/schemes.tgz"
OUT = sys.argv[2] if len(sys.argv) > 2 else "/tmp/dprofile.csv"

def parse_tab(text):
    """-> list of (a, b, c) signed 9-tuples, one per summand."""
    out, cur = [], []
    for ln in text.splitlines():
        if "|" not in ln:
            continue
        parts = [p.split() for p in ln.split("|")]
        if len(parts) != 3 or any(len(g) != 3 for g in parts):
            continue
        cur.append([[int(v) for v in g] for g in parts])
        if len(cur) == 3:
            a = tuple(v for r in cur for v in r[0])
            b = tuple(v for r in cur for v in r[1])
            c = tuple(v for r in cur for v in r[2])
            out.append((a, b, c))
            cur = []
    return out

def d_mod2(rows):
    s = {tuple(v & 1 for v in r) for r in rows}
    s.discard(tuple([0] * 9))
    return len(s)

def canon_sign(r):
    for v in r:
        if v:
            return tuple(-x for x in r) if v < 0 else tuple(r)
    return tuple(r)

def d_z(rows):
    s = {canon_sign(r) for r in rows}
    s.discard(tuple([0] * 9))
    return len(s)

rows_out = ["class,family,dA2,dB2,dC2,floor2,dAz,dBz,dCz,floorz"]
hist2 = collections.Counter()
le52, bad = [], []
named = {}
WATCH = ("i19w225c4efh", "i12w195c23ci", "i46w213c23ci", "i12w219c23ci",
         "i2w201c26fi", "i73w191c236f", "laderman")

with tarfile.open(TGZ, "r:gz") as tf:
    for m in tf:
        if not m.name.endswith(".tab"):
            continue
        cls = m.name.rsplit("/", 1)[-1].rsplit("-", 1)[0].replace(".tab", "")
        fam = m.name.split("/")[1] if "/" in m.name else ""
        text = tf.extractfile(m).read().decode()
        sm = parse_tab(text)
        if len(sm) != 23:
            bad.append((m.name, len(sm)))
            continue
        A = [t[0] for t in sm]; B = [t[1] for t in sm]; C = [t[2] for t in sm]
        d2 = (d_mod2(A), d_mod2(B), d_mod2(C))
        dz = (d_z(A), d_z(B), d_z(C))
        f2, fz = sum(d2) - 13, sum(dz) - 13
        rows_out.append(f"{cls},{fam},{d2[0]},{d2[1]},{d2[2]},{f2},"
                        f"{dz[0]},{dz[1]},{dz[2]},{fz}")
        hist2[f2] += 1
        if f2 <= 52:
            le52.append((f2, cls, d2, fam))
        for w in WATCH:
            if w in cls.lower() or w in cls:
                named[cls] = (d2, f2, dz, fz, fam)

with open(OUT, "w") as f:
    f.write("\n".join(rows_out) + "\n")

print(f"schemes parsed: {len(rows_out) - 1}   (skipped non-23: {len(bad)})")
for nm, ln in bad[:5]:
    print("  skipped:", nm, ln)
print("\nfloor2 histogram (basis-change-model adds floor, mod-2 d):")
for k in sorted(hist2):
    print(f"  {k}: {hist2[k]}")
print(f"\nclasses with floor2 <= 52: {len(le52)}")
for f2, cls, d2, fam in sorted(le52)[:40]:
    print(f"  floor {f2}  {cls}  d2={d2}  [{fam}]")
print("\nwatched classes:")
for cls, (d2, f2, dz, fz, fam) in sorted(named.items()):
    print(f"  {cls}: d2={d2} floor2={f2} | dz={dz} floorz={fz}")
