#!/bin/bash
# GEMM streams: the products of each lowest level as k single-threaded GEMM streams (M@k) against
# Accelerate's own threading, one product at a time (M); interleaved rounds
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm streams $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
v() { echo "$1,$1@2,$1@3,$1@4,$1@6"; }
./build/bench_fmm -n 4096 -t f -r 9 -m classical,$(v sw1),$(v dps48)
./build/bench_fmm -n 8192 -t f -r 7 -m classical,$(v dps48)
./build/bench_fmm -n 16384 -t f -r 5 -m $(v plan=SW/D48/G),dps48,dps48@3
./build/bench_fmm -n 4096 -t d -r 9 -m classical,$(v dps48)
./build/bench_fmm -n 8192 -t d -r 7 -m classical,$(v plan=SW/D48/G),dps48,dps48@3
./build/bench_fmm -n 16384 -t d -r 5 -m $(v dps48x2)
echo "# done $(date '+%H:%M')"
