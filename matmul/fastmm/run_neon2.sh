#!/bin/bash
# NEON products as whole products (each NEON thread packs B once per product), the same plans
# as run_neon.sh; interleaved rounds against Gk
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm NEON whole products $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
j() { local base=$1 k=$2; shift 2; local out="plan=$base/G$k"; for x in "$@"; do out="$out,plan=$base/G${k}N$x"; done; echo "$out"; }
./build/bench_fmm -n 8192 -t f -r 7 -m $(j D48 3 1 2 4)
./build/bench_fmm -n 4096 -t d -r 9 -m $(j D48 3 2 4 6 8)
./build/bench_fmm -n 8192 -t d -r 7 -m $(j SW/D48 3 2 4 6),$(j D48/D48 6 2 4 6 8)
./build/bench_fmm -n 16384 -t d -r 5 -m $(j SW/D48/D48 6 2 4 6)
echo "# done $(date '+%H:%M')"
