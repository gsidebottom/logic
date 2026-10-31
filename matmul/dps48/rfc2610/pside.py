#!/usr/bin/env python3
"""lns48 on P^T of every point in a directory written by pclasses.py: 12 procs, seeds x wall seconds, every
cost PLinOpt's (SLPchecker on the transposed program, so +32 is real, not assumed).

  pside.py DIR WALL SEEDS
"""
import json, os, sys
SP = "/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad"
os.environ.update(LNS_NAIVE="1", PLINOPT_BIN=f"{SP}/plinopt_main/bin", R48_SCRATCH=SP)
D = "/Users/greg/projects/logic/matmul/dps48"
sys.path.insert(0, f"{D}/patel"); sys.path.insert(0, D)
import sweep as SW
from concurrent.futures import ThreadPoolExecutor
d, wall, seeds = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
rows = json.load(open(f"{d}/classes.json"))
cands = {}
for r in rows:
    c = SW.Cand(f"{d}/{r['tag']}", 0, r['tag'], f"{d}/work"); c.stage_inputs(None); cands[r['tag']] = c
jobs = [(c, "Pt", s, wall, "P") for c in cands.values() for s in range(1, seeds + 1)]
res = {}
with ThreadPoolExecutor(12) as ex:
    for out in ex.map(lambda j: SW.job(*j), jobs):
        cand, side, cost = out[0], out[1], out[2]
        if cost is not None: res.setdefault(cand.tag, []).append(cost)
for r in rows: r["P"] = res.get(r["tag"], [])
json.dump(rows, open(f"{d}/pside.json", "w"))
print("class            canonical  nnz  non-unit   P costs")
for r in sorted(rows, key=lambda r: (min(r["P"] or [999]), -r["cP"])):
    print(f"{r['tag']:16s} {r['cP']:3d}     {r['nnz']:4d}  {r['nonunit']:4d}     {sorted(r['P'])}")
