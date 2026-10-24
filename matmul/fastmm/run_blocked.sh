#!/bin/bash
# fast schemes against the best classical variant (one GEMM, or blocked GEMMs of n/2, n/4, n/8)
cd "$(dirname "$0")" || exit 1
M=classical,blk2,blk4,blk8,sw1,sw2rec,sw3rec,sw2,dps48
echo "# bench_fmm blocked baselines $(date '+%Y-%m-%d %H:%M')"
for t in f d; do for n in 8192 16384; do ./build/bench_fmm -n $n -t $t -m $M -r 5; done; done
echo "# done $(date '+%H:%M')"
