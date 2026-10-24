#!/bin/bash
# the automatic plan choice against the named methods and the planner's runners-up, interleaved
# rounds; predictions from the cached calibration (results/calib_f32.txt, calib_f64.txt)
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm auto $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
for t in f d; do ./build/bench_fmm -n 16384 -t $t -p | grep -v '^#   '; done
B=classical,blk2
./build/bench_fmm -n 2048 -t f -r 9 -m $B,sw1,dps48,auto
./build/bench_fmm -n 4096 -t f -r 9 -m $B,sw1,dps48,auto
./build/bench_fmm -n 8192 -t f -r 7 -m $B,sw1,sw2rec,dps48,plan=SW/D48/G,auto
./build/bench_fmm -n 16384 -t f -r 5 -m $B,sw3rec,dps48,dps48sw,dps48x2,plan=SW/D48/G,auto
./build/bench_fmm -n 2048 -t d -r 9 -m $B,sw1,dps48,auto
./build/bench_fmm -n 4096 -t d -r 9 -m $B,sw1,sw2rec,dps48,auto
./build/bench_fmm -n 8192 -t d -r 7 -m $B,sw3rec,dps48,dps48sw,dps48x2,plan=SW/D48/G,auto
./build/bench_fmm -n 16384 -t d -r 5 -m $B,sw4rec,dps48sw,dps48x2,plan=SW/SW/D48/G,plan=SW/D48/SW/G,auto
echo "# done $(date '+%H:%M')"
