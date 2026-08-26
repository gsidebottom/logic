#!/usr/bin/env python3
"""Export Wang's 496 verified A-side orbit bounds (cert_matrix_q02_n333) as a
plain-text table for subgame.rs's --wang-table leaf rule, plus the 14 dim-2
orbit bases (the rank-21 gating layer) with their recorded bounds.

Format, one orbit per line:  <bound>:<row1,row2,...>   (u16 rows; the
unconstrained root orbit has an empty row list: "20:").
"""
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from koszul_vs_wang import parse_bytes, CERT

# Strongest verified bounds: our 30x-cascade output (verified by his
# verifier 2026-08-25) unless overridden; falls back to the shipped cert.
CASCADE = "/Users/greg/projects/trlb-wang/probe/cert_full_out.pb.txt"
src = sys.argv[1] if len(sys.argv) > 1 else (CASCADE if os.path.exists(CASCADE) else CERT)
print(f"source: {src}")
txt = open(src).read()
blocks = re.findall(r"constrained_tensors \{(.*?)\n\}", txt, re.S)
table, dim2 = [], []
for b in blocks:
    lbm = re.search(r"rank_lower_bound: (\d+)", b)
    if lbm is None:
        continue
    lb = int(lbm.group(1))
    cm = re.search(r'constraints: "((?:[^"\\]|\\.)*)"', b)
    U = []
    if cm:
        by = parse_bytes(cm.group(1))
        U = [by[i] | (by[i + 1] << 8) for i in range(0, len(by), 2)]
    table.append((lb, U))
    if len(U) == 2:
        dim2.append((lb, U))

assert len(table) == 496, len(table)
assert len(dim2) == 14, len(dim2)
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "wang_table_n333.txt")
with open(out, "w") as f:
    for lb, U in table:
        f.write(f"{lb}:{','.join(map(str, U))}\n")
print(f"wrote {out}: 496 orbits")
print("dim-2 gating layer (bound: rows):")
for i, (lb, U) in enumerate(dim2):
    print(f"  {i:2d}  {lb}: --root-u {U[0]},{U[1]}")
