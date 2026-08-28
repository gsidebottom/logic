#!/bin/zsh
# (c) campaign: mixed-play ladders on Wang's 14 dim-2 orbits, standing on his
# verified A-side orbit table as leaf oracle. Each orbit: k = table+1.
set -e
cd /Users/greg/projects/logic
BIN=./target/release/subgame
TBL=matmul/r22/wang_table_n333.txt
# rows bound  (order: the six 18s first, then the eight 19s)
ORBITS=(
  "1,2 18" "1,10 18" "1,16 18" "1,20 18" "1,84 18" "1,160 18"
  "10,19 19" "10,20 19" "10,68 19" "10,84 19" "10,96 19" "10,258 19" "10,275 19" "84,163 19"
)
i=0
for spec in $ORBITS; do
  rows=${spec% *}; bd=${spec#* }; k=$((bd+1))
  log=matmul/r22/campaign_abc_orbit${i}_k${k}.log
  echo "=== orbit $i (u=$rows, table $bd) ladder k=$k start $(date +%H:%M:%S) ==="
  $BIN --n 3 --sym --wang-table $TBL --root-u $rows \
    --ladder --from $k --to $k --sides ABC --par 4 \
    --time 3600 --nodes 200000000 --heartbeat 120 > $log 2>&1 || true
  grep -E "k=$k: |CAP|=> " $log | tail -3
  i=$((i+1))
done
echo "ABC CAMPAIGN DONE $(date +%H:%M:%S)"
