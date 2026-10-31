#!/bin/bash
# lns48 sweep over Sedoglavic's 160 decompositions (TensorDecompositions.tgz, Oct 23), with the record
# family as a control: all at 30 s per side, best 24 at 120 s, best 6 at 300 s x 2.  L, R and P^T each
# from naive matrix seeds, every count PLinOpt's (SLPchecker).  Bounded by timeout 5400.
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad; D=/Users/greg/projects/logic/matmul/dps48; W=$SP/td; PY=/usr/bin/python3
cd $D
$PY - "$W" "$D" "$SP" <<'PYEOF'
import csv, sys
W, D, SP = sys.argv[1:4]
rows = []
for r in csv.DictReader(open(W + "/score.csv")):
    rows.append(dict(rank=len(rows), floor=r["floor"], fl=r["fl"], fr=r["fr"], fp=r["fp"], nonunit=r["nonunit"], objective=0, prefix=f"{W}/pts/{r['tag']}"))
for p, f in ((f"{D}/cand48/lam01c0_201", 150), (f"{SP}/plinopt_main/data/4x4x4_48_204", 146)):
    rows.append(dict(rank=len(rows), floor=f, fl=0, fr=0, fp=38, nonunit=0, objective=0, prefix=p))
with open(W + "/pool.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
print(len(rows), "points in the pool")
PYEOF
echo "# sweep start $(date '+%Y-%m-%d %H:%M')"
LNS_NAIVE=1 PLINOPT_BIN=$SP/plinopt_main/bin R48_SCRATCH=$SP /usr/bin/env timeout 5400 $PY patel/sweep.py --out $W/sweep --pool $W/pool.csv --procs 12 --a-seconds 30 --b-seconds 120 --c-seconds 300 --a-keep 24 --b-keep 6 2>&1 | grep -v "^$" | cut -c1-200
echo "sweep exit ${PIPESTATUS[0]}"
echo "# done $(date '+%H:%M')"
