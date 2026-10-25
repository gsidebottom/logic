#!/bin/bash
# the accuracy budget: predicted against measured errors over plans of 0-3 fused levels (in f32
# also against an f64 product of the same inputs, FMM_EXACT=1), and auto under growth budgets
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm accuracy budget $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
M=classical,sw1,dps48,sw2rec,plan=SW/D48/G3,dps48x2@6,plan=SW/D48/D48/G6,auto,auto:16,auto:8,auto:2
for n in 4096 8192 16384; do FMM_EXACT=1 ./build/bench_fmm -n $n -t f -r 3 -m $M; done
for n in 4096 8192 16384; do ./build/bench_fmm -n $n -t d -r 3 -m $M; done
echo "# done $(date '+%H:%M')"
