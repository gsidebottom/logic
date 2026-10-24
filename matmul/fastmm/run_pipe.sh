#!/bin/bash
# pipelined levels (X+p: the passes of the neighbouring sub-problems on p threads while the GEMM
# streams of one run) against the same plans run level by level; interleaved rounds
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm pipelined passes $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
p() { local top=$1 rest=$2; local out="plan=$top/$rest"; for x in 1 2 3 4; do out="$out,plan=$top+$x/$rest"; done; echo "$out"; }
./build/bench_fmm -n 8192 -t f -r 7 -m plan=D48/G3,$(p SW D48/G3)
./build/bench_fmm -n 16384 -t f -r 5 -m $(p D48 D48/G6),$(p SW D48/G3)
./build/bench_fmm -n 4096 -t d -r 9 -m $(p SW D48/G6),$(p D48 D48/G6)
./build/bench_fmm -n 8192 -t d -r 7 -m $(p D48 D48/G6),$(p SW D48/G3)
./build/bench_fmm -n 16384 -t d -r 5 -m plan=SW/D48/D48/G6,plan=SW/D48+1/D48/G6,plan=SW/D48+2/D48/G6,plan=SW/D48+3/D48/G6,plan=SW/D48+4/D48/G6
echo "# done $(date '+%H:%M')"
