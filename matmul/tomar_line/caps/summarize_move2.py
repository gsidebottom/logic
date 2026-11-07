#!/usr/bin/env python3
"""Table of the move-2 CaDiCaL campaign: instance x variant, status and seconds per seed.
usage: summarize_move2.py m2_chain.log"""
import sys, re
from collections import defaultdict
rows = defaultdict(dict)
for line in open(sys.argv[1]):
    m = re.match(r'(\S+)\s+seed (\d+)\s+(\S+)\s+([\d.]+) s', line)
    if not m:
        continue
    name, sd, st, sec = m.group(1), int(m.group(2)), m.group(3), float(m.group(4))
    inst, var = name.rsplit('_', 1)
    rows[inst][(var, sd)] = (st, sec)
variants = ['none', 'entries', 'caps', 'all']
print(f"{'instance':<18}" + ''.join(f"{v:>22}" for v in variants))
for inst in sorted(rows):
    cells = []
    for v in variants:
        parts = []
        for sd in (1, 2):
            if (v, sd) in rows[inst]:
                st, sec = rows[inst][(v, sd)]
                parts.append(f"{st[:5]} {sec:.0f}s")
        cells.append(' | '.join(parts) if parts else '-')
    print(f"{inst:<18}" + ''.join(f"{c:>22}" for c in cells))
