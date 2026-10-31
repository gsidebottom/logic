#!/bin/bash
# After the main sweep: lns48 on the 24 frame-triple points and the two accuracy points as controls.
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad; D=/Users/greg/projects/logic/matmul/dps48; W=$SP/td; PY=/usr/bin/python3
for i in $(seq 1 150); do grep -q "^# done" /private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/run_vl.log && break; sleep 30; done
cd $D
$PY - "$W" "$SP" <<'PYEOF'
import csv, json, sys
W, SP = sys.argv[1:3]
rows = []
for r in json.load(open(W + "/perfect/score.json")):
    rows.append(dict(rank=len(rows), floor=r["floor"], fl=r["fl"], fr=r["fr"], fp=r["fp"], nonunit=r["nonunit"], objective=0, prefix=f"{W}/perfect/{r['tag']}"))
for n, f in (("accurate_262", 168), ("accurate", 168)):
    rows.append(dict(rank=len(rows), floor=f, fl=0, fr=0, fp=0, nonunit=0, objective=0, prefix=f"{SP}/plinopt_main/data/4x4x4_48_{n}"))
with open(W + "/pool_perfect.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
PYEOF
echo "# perfect sweep start $(date '+%H:%M')"
LNS_NAIVE=1 PLINOPT_BIN=$SP/plinopt_main/bin R48_SCRATCH=$SP /usr/bin/env timeout 1800 $PY patel/sweep.py --out $W/sweep_perfect --pool $W/pool_perfect.csv --procs 12 --a-seconds 30 --b-seconds 120 --c-seconds 300 --a-keep 6 --b-keep 2 2>&1 | grep -v "^$" | cut -c1-200
echo "sweep exit ${PIPESTATUS[0]}"
echo "# done $(date '+%H:%M')"
