#!/bin/bash
# the automatic plan choice with GEMM streams and pipelined levels against the best plans found
# by hand and the planner's runners-up (pass threads 2, 3, 4 calibrated); interleaved rounds
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm auto with pipelines $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
for t in f d; do ./build/bench_fmm -n 16384 -t $t -p | grep -v '^#   '; done
./build/bench_fmm -n 2048 -t f -r 9 -m classical,dps48@6,auto
./build/bench_fmm -n 4096 -t f -r 9 -m classical,dps48@6,plan=SW+4/D48/G6,auto
./build/bench_fmm -n 8192 -t f -r 7 -m classical,dps48@3,plan=D48+4/D48/G6,plan=SW+4/D48/G6,plan=SW+2/D48/G3,auto
./build/bench_fmm -n 16384 -t f -r 5 -m blk2,plan=D48/D48/G6,plan=D48+4/D48/G6,plan=D48+2/D48/G6,plan=SW/D48+4/D48/G6,plan=SW/D48/G3,auto
./build/bench_fmm -n 2048 -t d -r 9 -m classical,dps48@6,auto
./build/bench_fmm -n 4096 -t d -r 9 -m classical,dps48@3,plan=SW/D48/G6,plan=D48+4/D48/G6,plan=SW+4/D48/G6,auto
./build/bench_fmm -n 8192 -t d -r 7 -m classical,plan=D48/D48/G6,plan=D48+2/D48/G6,plan=D48+4/D48/G6,plan=D48+4/D48/G3,auto
./build/bench_fmm -n 16384 -t d -r 5 -m blk2,plan=SW/D48/D48/G6,plan=SW/D48+2/D48/G6,plan=SW/D48+4/D48/G6,plan=D48/SW+4/D48/G6,auto
echo "# done $(date '+%H:%M')"
