#!/bin/bash
# the automatic plan choice with GEMM streams (leaf Gk: a level's products as k single-threaded
# streams) against the best plans without streams and the planner's runners-up; interleaved rounds
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm auto with streams $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
for t in f d; do ./build/bench_fmm -n 16384 -t $t -p | grep -v '^#   '; done
./build/bench_fmm -n 2048 -t f -r 9 -m classical,sw1@3,dps48@6,auto
./build/bench_fmm -n 4096 -t f -r 9 -m classical,sw1@3,dps48,dps48@3,dps48@6,auto
./build/bench_fmm -n 8192 -t f -r 7 -m classical,dps48,dps48@3,dps48@4,plan=SW/D48/G6,auto
./build/bench_fmm -n 16384 -t f -r 5 -m blk2,plan=SW/D48/G,plan=SW/D48/G3,dps48x2@3,dps48x2@6,dps48sw@3,auto
./build/bench_fmm -n 2048 -t d -r 9 -m classical,sw1,dps48,dps48@3,dps48@6,auto
./build/bench_fmm -n 4096 -t d -r 9 -m classical,dps48,dps48@3,plan=SW/D48/G3,plan=SW/D48/G6,auto
./build/bench_fmm -n 8192 -t d -r 7 -m classical,plan=SW/D48/G,plan=SW/D48/G3,dps48x2@3,dps48x2@6,plan=SW/SW/D48/G6,auto
./build/bench_fmm -n 16384 -t d -r 5 -m blk2,dps48x2,dps48x2@3,plan=SW/D48/D48/G3,plan=SW/D48/D48/G6,plan=D48/SW/D48/G6,auto
echo "# done $(date '+%H:%M')"
