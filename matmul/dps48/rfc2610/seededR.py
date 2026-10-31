#!/usr/bin/env python3
"""More seeds of lns48 from accurate_262's published R program, for diversity among low-cost programs.

  seededR.py WALL FIRST LAST
"""
import os, sys
SP = "/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad"
os.environ.update(LNS_NAIVE="1", PLINOPT_BIN=f"{SP}/plinopt_main/bin", R48_SCRATCH=SP)
D = "/Users/greg/projects/logic/matmul/dps48"
sys.path.insert(0, f"{D}/patel"); sys.path.insert(0, D)
import sweep as SW
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
wall, a, b = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
pre = f"{SP}/plinopt_main/data/4x4x4_48_accurate_262"
c = SW.Cand(pre, 168, "a262", f"{SP}/td/seeded"); c.stage_inputs(None)
c.seed_prog = {"R": pre + "_R.slp"}
with ThreadPoolExecutor(12) as ex:
    res = [r[2] for r in ex.map(lambda s: SW.job(c, "R", s, wall, "S"), range(a, b + 1))]
print(sorted(Counter(res).items(), key=lambda kv: str(kv[0])))
