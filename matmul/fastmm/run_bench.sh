#!/bin/bash
# scaling sweep of bench_fmm (interleaved rounds, scratch padding on): f32 at 2048..16384 (every method), f64 at 2048..8192 (every
# method) and 16384 (no op-by-op run, to stay within memory)
cd "$(dirname "$0")" || exit 1
ALL=classical,sw1,sw2rec,sw3rec,sw2,dps48,dps48ops
echo "# bench_fmm sweep $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string), $(($(sysctl -n hw.memsize) / 1073741824)) GB"
for n in 2048 4096 8192 16384; do ./build/bench_fmm -n $n -t f -m $ALL -r $([ $n -le 8192 ] && echo 7 || echo 5); done
for n in 2048 4096 8192; do ./build/bench_fmm -n $n -t d -m $ALL -r 7; done
./build/bench_fmm -n 16384 -t d -m classical,sw1,sw2rec,sw3rec,sw2,dps48 -r 5
echo "# sweep done $(date '+%H:%M')"
