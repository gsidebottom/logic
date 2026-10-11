#!/usr/bin/env python3
"""Emit signed leg files (.slegs: 23 lines of 9 integers) for fbsmin
from a DB .tab inside schemes.tgz.

Usage: emit_slegs.py schemes.tgz 'schemes/<family>/<class>-000.tab' outprefix
Writes outprefix_{A,B,C}.slegs in tab product order.
"""
import sys, tarfile

TGZ, TAB, OUT = sys.argv[1:4]

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

sm = parse_tab(tarfile.open(TGZ, "r:gz").extractfile(TAB).read().decode())
assert len(sm) == 23, len(sm)
for side, nm in enumerate("ABC"):
    with open(f"{OUT}_{nm}.slegs", "w") as f:
        for t in sm:
            f.write(" ".join(str(v) for v in t[side]) + "\n")
    print(f"{OUT}_{nm}.slegs")
