#!/bin/bash
# Middle-basis annealing (orbit48 --factors Y, P unchanged) at the cheap P classes outside the record's, then lns48 on
# L and R with each point's P charged at its class cost.  A 200 needs L + R <= 200 - P.
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad; D=/Users/greg/projects/logic/matmul/dps48; W=$SP/td/yc; PY=/usr/bin/python3
rm -rf $W; mkdir -p $W; cd $D
echo "# Y-only at the cheap P classes, $(date '+%Y-%m-%d %H:%M')"
for c in c10_n264_4 c10_n260_2 c10_n260_1 c10_n260_3; do for lam in 0.05 0.1 0.3; do
  (/usr/bin/env timeout 1200 $PY orbit48.py $SP/td/pcl/$c $W/y_${c}_l$lam --factors Y --lam $lam --keep 15 --pool-floor 175 --seed 1 > $W/y_${c}_l$lam.log 2>&1) &
done; done; wait
echo "## annealing done $(date '+%H:%M')"
$PY - "$W" <<'PYEOF'
import csv, glob, hashlib, os, sys
W = sys.argv[1]
cost = {"c10_n264_4": 88, "c10_n260_2": 88, "c10_n260_1": 88, "c10_n260_3": 89}
seen, rows = set(), []
for f in sorted(glob.glob(W + "/y_*/candidates.csv")):
    c = os.path.basename(os.path.dirname(f))[2:].split("_l")[0]
    for r in csv.DictReader(open(f)):
        h = hashlib.md5(open(r["prefix"] + "_L.sms", "rb").read() + open(r["prefix"] + "_R.sms", "rb").read()).hexdigest()
        if h in seen: continue
        seen.add(h); r["fixedp"] = cost[c]; rows.append(r)
with open(W + "/pool.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
print(len(rows), "distinct points; floors", sorted(set(int(r["floor"]) for r in rows))[:6], "by class", {c: sum(1 for r in rows if r["fixedp"] == p) for c, p in cost.items()})
PYEOF
echo "## sweep $(date '+%H:%M')"
LNS_NAIVE=1 FIXED_P=88 PLINOPT_BIN=$SP/plinopt_main/bin R48_SCRATCH=$SP /usr/bin/env timeout 3600 $PY patel/sweep.py --out $W/sweep --pool $W/pool.csv --procs 12 --a-seconds 30 --b-seconds 120 --c-seconds 300 --a-keep 24 --b-keep 6 2>&1 | grep -v "^$" | cut -c1-200
echo "sweep exit ${PIPESTATUS[0]}"
echo "# done $(date '+%H:%M')"
