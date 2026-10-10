#!/usr/bin/env python3
"""Emit the six 23x9 leg files (A/B/C side masks, mod 2) for the
free-basis minimizer `fbmin`: our 55-add record class i19w225c4efh and
Nielsen's base class i12w195c23ci (arXiv 2609.06588), straight from the
HKS DB tarball. The free-basis minimum is invariant under the de Groote
sandwich action (it acts on each leg by an invertible column map), so
any representative of the class gives the same six answers.

Usage: fbmin_legs.py [schemes.tgz] [outdir]
Writes <outdir>/<class>_{A,B,C}.legs: one 9-char 0/1 mask per line
(row-major 3x3 factor, all 23 rows; fbmin dedups).
"""
import sys, tarfile, pathlib

TGZ = sys.argv[1] if len(sys.argv) > 1 else "dbcache/schemes.tgz"
OUT = pathlib.Path(sys.argv[2] if len(sys.argv) > 2 else ".")

WANT = {
    "schemes/18x2+51x+4y6+6y4+13y3+z32+z28+z27/i19w225c4efh-000.tab": "i19w225c4efh",
    "schemes/17x2+52x+4y6+5y4+14y3+z32+2z27/i12w195c23ci-000.tab": "i12w195c23ci",
}

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
            out.append(tuple(
                tuple(v for r in cur for v in r[s]) for s in range(3)))
            cur = []
    return out

found = 0
with tarfile.open(TGZ, "r:gz") as tf:
    for m in tf:
        if m.name not in WANT:
            continue
        cls = WANT[m.name]
        sm = parse_tab(tf.extractfile(m).read().decode())
        assert len(sm) == 23, (m.name, len(sm))
        for side, nm in enumerate("ABC"):
            rows = ["".join(str(v & 1) for v in t[side]) for t in sm]
            assert all(r != "0" * 9 for r in rows), "zero factor row"
            d = len(set(rows))
            path = OUT / f"{cls}_{nm}.legs"
            path.write_text("\n".join(rows) + "\n")
            print(f"{path}  d={d}")
        found += 1
assert found == 2, f"found only {found} of 2 class tabs"
