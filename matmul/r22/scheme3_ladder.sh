#!/bin/zsh
# 3x3 UNSAT ladder, parallel (12 threads): probe arm climbs; one plain r=11
# for the record (plain ceiling established at 10).
cd /Users/greg/projects/logic
B=./target/release/schemesearch3
echo "=== r=11 plain (cap 600s) $(date +%H:%M:%S) ==="
$B --r 11 --time 600 --threads 12 2>&1 | tail -1
for spec in "11 3600" "12 7200" "13 14400"; do
  r=${spec% *}; cap=${spec#* }
  echo "=== r=$r sub-probe (cap ${cap}s) $(date +%H:%M:%S) ==="
  $B --r $r --time $cap --threads 12 --sub-probe --probe-min-remaining 3 2>&1 | tail -1
done
echo "LADDER DONE $(date +%H:%M:%S)"
