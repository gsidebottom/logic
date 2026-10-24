#!/bin/bash
# NEON products beside the GEMM streams: leaf GkNj gives a level's last j products to NEON GEMMs
# on FMM_NEON_THREADS more cores (default 4), in row slabs (128 rows f32, 64 f64; each slab packs
# all of B again); interleaved rounds against Gk.  run_neon2.sh: whole products instead
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm NEON products $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
j() { local base=$1 k=$2; shift 2; local out="plan=$base/G$k"; for x in "$@"; do out="$out,plan=$base/G${k}N$x"; done; echo "$out"; }
FMM_NEON_SLAB=128 ./build/bench_fmm -n 4096 -t f -r 9 -m $(j D48 6 2 4 6)
FMM_NEON_SLAB=128 ./build/bench_fmm -n 8192 -t f -r 7 -m $(j D48 3 2 4 6 8)
FMM_NEON_SLAB=128 ./build/bench_fmm -n 16384 -t f -r 5 -m $(j SW/D48 3 2 4 6)
FMM_NEON_SLAB=64 ./build/bench_fmm -n 4096 -t d -r 9 -m $(j D48 3 2 4 6 8 10)
FMM_NEON_SLAB=64 ./build/bench_fmm -n 8192 -t d -r 7 -m $(j SW/D48 3 4 6 8 10),$(j D48/D48 6 4 8)
FMM_NEON_SLAB=64 FMM_NEON_THREADS=2 ./build/bench_fmm -n 8192 -t d -r 7 -m $(j SW/D48 3 2 4 6)
FMM_NEON_SLAB=64 ./build/bench_fmm -n 16384 -t d -r 5 -m $(j SW/D48/D48 6 4 8 12)
echo "# done $(date '+%H:%M')"
