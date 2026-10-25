#!/bin/bash
# two-level pipelines (X+/Z+p/Y/Gk: Z's own passes in the background of the neighbouring
# products' pipelines) against one-level pipelines; interleaved rounds
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm two-level pipelines $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
./build/bench_fmm -n 8192 -t d -r 7 -m plan=D48+3/D48/G6,plan=SW/D48+3/D48/G6,plan=SW+/D48+3/D48/G6
./build/bench_fmm -n 16384 -t f -r 5 -m plan=D48+3/D48/G6,plan=SW/D48+3/D48/G6,plan=SW+/D48+3/D48/G6,plan=SW/D48+4/D48/G6,plan=SW+/D48+4/D48/G6
./build/bench_fmm -n 16384 -t d -r 5 -m plan=SW/D48+3/D48/G6,plan=SW+/D48+3/D48/G6,plan=SW/D48+4/D48/G6,plan=SW+/D48+4/D48/G6,plan=D48/D48+4/D48/G6,plan=D48+/D48+4/D48/G6
echo "# done $(date '+%H:%M')"
