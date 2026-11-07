#!/bin/zsh
# The overnight 4x4 descent (2026-11-07, 05:16-08:16): 3 h from all four projection pools of AlphaTensor's
# rank-63 schemes (<4,4,5> by col, <4,5,4> by inner-a and inner-b, <5,4,4> by row; 1500 seeds at 59 each,
# the rotated inputs made by matmul/rotate_f2.py, the pools by make_pools.sh / project_f2.py), aiming at 46
# and writing every 47.  Ran at background priority (efficiency cores) beside the lower-bound climb.
# Result: 65,162 landings from 28,498 trajectories, 22 distinct 47s (found47_d180), 13,757 48s, 18,198 49s, no 46.
set -u
L=/Users/greg/projects/logic
SEEDS=$1   # directory with the 6000 .bits seeds
OUT=$2
mkdir -p "$OUT"
taskpolicy -c background /opt/homebrew/bin/timeout 11400s $L/target/release/flip 4 4 4 --seeds-dir "$SEEDS" --save-at 49 --write-at 47 --record 47 --minutes 180 --threads 12 --seed 13 --out "$OUT" --lift-below 0 --group-moves 0 > "$OUT.log" 2>&1
