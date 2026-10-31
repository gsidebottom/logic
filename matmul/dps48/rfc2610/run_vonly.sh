#!/bin/bash
# V-only search with P fixed at 89: anneal the middle factor alone (orbit48 --factors Y, which leaves P
# unchanged) from the four known points of the 89 family, then search L and R with lns48 at the best
# points (sweep.py, FIXED_P=89: 30 s, best 30 at 120 s, best 8 at 600 s x 2).  A 200 needs L + R <= 111.
# The four start points go through the sweep too, as a control: they should reach 112, 112, 112, 114.
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
D=/Users/greg/projects/logic/matmul/dps48; W=$SP/vonly; PY=/usr/bin/python3
rm -rf $W; mkdir -p $W; cd $D
echo "# V-only search, $(date '+%Y-%m-%d %H:%M')"
srcs="lam01c0:$D/cand48/lam01c0_201 p005:$D/cand48/p005_201n p010:$D/cand48/p010_201 j203:$SP/rfc2610/files/4x4x4_48_203"
for s in $srcs; do n=${s%%:*}; p=${s#*:}; for lam in 0.05 0.1 0.3 0.5; do
  (/usr/bin/env timeout 1500 $PY orbit48.py $p $W/y_${n}_l$lam --factors Y --lam $lam --keep 15 --pool-floor 170 --seed 1 > $W/y_${n}_l$lam.log 2>&1) &
done; done; wait
echo "## annealing done $(date '+%H:%M'): $(ls -d $W/y_*/ | wc -l | tr -d ' ') pools"
$PY - "$W" $srcs <<'PYEOF'
import csv, glob, hashlib, os, sys
from fractions import Fraction as Fr
W, srcs = sys.argv[1], dict(s.split(":", 1) for s in sys.argv[2:])
def P(pre):
    rows = [l.split() for l in open(pre + "_P.sms") if l.strip() and not l.startswith('#')]
    return {(t[0], t[1]): Fr(t[2]) for t in rows[1:] if len(t) == 3 and t[0] != '0'}
seen, out, moved = set(), [], 0
rows = [dict(rank=-1, floor=0, fl=0, fr=0, fp=38, nonunit=0, objective=0, prefix=p) for p in srcs.values()]
for f in sorted(glob.glob(W + "/y_*/candidates.csv")):
    n = os.path.basename(os.path.dirname(f)).split("_")[1]
    p0 = P(srcs[n])
    for r in csv.DictReader(open(f)):
        moved += P(r["prefix"]) != p0
        rows.append(r)
for r in rows:
    h = hashlib.md5(open(r["prefix"] + "_L.sms", "rb").read() + open(r["prefix"] + "_R.sms", "rb").read()).hexdigest()
    if h not in seen: seen.add(h); out.append(r)
with open(W + "/pool.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=["rank", "floor", "fl", "fr", "fp", "nonunit", "objective", "prefix"]); w.writeheader(); w.writerows(out)
fl = sorted(int(r["floor"]) for r in out if int(r["floor"]))
print(f"pool: {len(rows)} points, {len(out)} distinct; candidates whose P differs from their source: {moved}; floors {fl[0]}..{fl[-1]}; side floors P: {sorted(set(str(r['fp']) for r in out))}")
PYEOF
echo "## sweep $(date '+%H:%M')"
LNS_NAIVE=1 FIXED_P=89 PLINOPT_BIN=$SP/plinopt_main/bin R48_SCRATCH=$SP /usr/bin/env timeout 5400 $PY patel/sweep.py --out $W/sweep --pool $W/pool.csv --procs 12 --a-seconds 30 --b-seconds 120 --c-seconds 600 --a-keep 30 --b-keep 8 2>&1 | grep -v "^$" | cut -c1-200 | tail -40
echo "sweep exit ${PIPESTATUS[0]}"
echo "# done $(date '+%H:%M')"
