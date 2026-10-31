#!/usr/bin/env python3
"""lns48 from the published accurate_262 programs (L, R, P^T), 12 seeds x WALL seconds per side: can the
published 72 + 78 + 112 be improved at the same accuracy?  Every count is PLinOpt's.

  seeded262.py WALL PtSLP
"""
import os, sys
SP = "/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad"
os.environ.update(LNS_NAIVE="1", PLINOPT_BIN=f"{SP}/plinopt_main/bin", R48_SCRATCH=SP)
D = "/Users/greg/projects/logic/matmul/dps48"
sys.path.insert(0, f"{D}/patel"); sys.path.insert(0, D)
import sweep as SW
from concurrent.futures import ThreadPoolExecutor
wall, pt = float(sys.argv[1]), sys.argv[2]
pre = f"{SP}/plinopt_main/data/4x4x4_48_accurate_262"
c = SW.Cand(pre, 168, "a262", f"{SP}/td/seeded"); c.stage_inputs(None)
c.seed_prog = {"L": pre + "_L.slp", "R": pre + "_R.slp", "Pt": pt}
jobs = [(c, s, sd, wall, "S") for s in ("L", "R", "Pt") for sd in range(1, 13)]
res = {}
with ThreadPoolExecutor(12) as ex:
    for cand, side, cost, best in ex.map(lambda j: SW.job(*j), jobs):
        res.setdefault(side, []).append(cost)
print("published L 72, R 78, P 112")
for s, v in res.items(): print(f"  {s}: best {min(x for x in v if x is not None)}  all {sorted(x for x in v if x is not None)}  failures {sum(x is None for x in v)}")
