#!/bin/zsh
# Exhaustion calibration: ladder table+1 on samples of dim-4 and dim-3 orbits
# (small downstream spaces) to fit exhaustion node-counts vs quotient dim,
# extrapolating the budget a dim-2/1/0 PROVED/FAILS verdict needs.
# Stage 1: 8 dim-4 orbits (5-dim A-quotient), 45 min cap.
# Stage 2: 6 dim-3 orbits (6-dim A-quotient), 2 h cap.
set -e
cd /Users/greg/projects/logic
BIN=./target/release/subgame
TBL=matmul/r22/wang_table_n333.txt

# orbit lists from the table itself: "<bound>:<r1,r2,...>", dim = #rows
python3 - <<'PY' > matmul/r22/calib_roots.txt
for line in open("matmul/r22/wang_table_n333.txt"):
    b, rows = line.strip().split(":")
    rs = [r for r in rows.split(",") if r]
    if len(rs) in (3, 4):
        print(f"{len(rs)} {b} {','.join(rs)}")
PY
i=0
grep '^4 ' matmul/r22/calib_roots.txt | head -8 | while read dim bd rows; do
  k=$((bd+1))
  log=matmul/r22/calib_d4_${i}_k${k}.log
  echo "=== calib dim-4 #$i (u=$rows, table $bd) k=$k start $(date +%H:%M:%S) ==="
  $BIN --n 3 --sym --wang-table $TBL --root-u $rows --ladder --from $k --to $k \
    --sides AB --par 4 --time 2700 --nodes 500000000 --heartbeat 300 > $log 2>&1 || true
  grep -E "k=$k: " $log | tail -1
  i=$((i+1))
done
i=0
grep '^3 ' matmul/r22/calib_roots.txt | head -6 | while read dim bd rows; do
  k=$((bd+1))
  log=matmul/r22/calib_d3_${i}_k${k}.log
  echo "=== calib dim-3 #$i (u=$rows, table $bd) k=$k start $(date +%H:%M:%S) ==="
  $BIN --n 3 --sym --wang-table $TBL --root-u $rows --ladder --from $k --to $k \
    --sides AB --par 4 --time 7200 --nodes 500000000 --heartbeat 300 > $log 2>&1 || true
  grep -E "k=$k: " $log | tail -1
  i=$((i+1))
done
echo "CALIBRATION DONE $(date +%H:%M:%S)"
