#!/bin/zsh
# The 2x2 level at DPS's optimum in Q(sqrt 3) against the library's dyadic point (2026-11-22).  Three binaries,
# otherwise identical: dps7 (build/bench_fmm_dps7: the dyadic point, PLinOpt-optimized programs, the library's
# until 2026-11-22; the run of that day used build/bench_fmm, then the same kernels),
# dps7d (build/bench_fmm_sw_dps7d: the dyadic point as direct sums, the control for the programs' form) and
# q3 (build/bench_fmm_sw_q3: the Q(sqrt 3) point as direct sums, constants rounded to double; sw_points.py).
# Errors against the exact product (FMM_EXACT: f32 the f64 product, f64 the compensated product), four random
# instances (FMM_SEED).  Phase 1: the level alone and recursively.  Phase 2: the plans with a 2x2 level on top
# of Table "tab:sw" of the report, by name (no calibration is read or written: FMM_CALIB_DIR is an empty
# scratch directory).  Build first: make build/bench_fmm_dps7 build/bench_fmm_sw_dps7d build/bench_fmm_sw_q3
# Output: results/sw_q3_2026-11-22.txt
cd "$(dirname "$0")" || exit 1
SP=${SW_Q3_SCRATCH:?set SW_Q3_SCRATCH to a scratch directory for the reference cache}
mkdir -p "$SP/ref" "$SP/calib"
unset FMM_INPUT FMM_PRESCALE
export FMM_EXACT=1 FMM_REFCACHE=$SP/ref FMM_CALIB_DIR=$SP/calib
typeset -A BIN; BIN=(dps7 bench_fmm_dps7 dps7d bench_fmm_sw_dps7d q3 bench_fmm_sw_q3)
echo "# the 2x2 level: dps7 (dyadic point, optimized programs) / dps7d (dyadic point, direct sums) / q3 (Q(sqrt 3) point, direct sums); $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
run() {   # n precision rounds seed methods
  for v in dps7 dps7d q3; do
    echo "### $v n=$1 $2 seed=$4  $(date '+%H:%M')"
    FMM_SEED=$4 timeout 900 ./build/$BIN[$v] -n $1 -t $2 -r $3 -m $5 | grep -v '^#   '
  done
}
for n in 4096 8192; do for t in f d; do for seed in 0 1 2 3; do
  echo "## phase 1: the level alone and recursively, n=$n $t seed=$seed"
  run $n $t 3 $seed classical,sw1,sw2rec,sw3rec,sw4rec
done; done; done
for seed in 0 1 2 3; do
  echo "## phase 2: plans with a 2x2 level on top, seed=$seed"
  run 3456 d 3 $seed classical,plan=SW+3/R363/G6
  run 6912 d 3 $seed classical,plan=SW/R363/G6
  run 6912 f 3 $seed classical,plan=SW/D48+2/D48/G6
done
for seed in 0 1; do
  echo "## phase 2: plans with a 2x2 level on top at 13824, seed=$seed"
  run 13824 d 2 $seed classical,plan=SW/R363+3/R633/G6
  run 13824 f 2 $seed classical,plan=SW/D48+2/D48/G6
done
echo "# top CPU users after the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
echo "# done $(date '+%H:%M')"
