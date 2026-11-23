#!/bin/zsh
# The R363 level (DPS's accurate <3x6x3:40>) at other points of its orbit (orbit_points.py), against the library's
# (2026-11-22).  Three binaries, otherwise identical: dps (build/bench_fmm: DPS's point, schemes/opt/r363_*,
# amplification ratio 2.55), h (build/bench_fmm_rs_r363h: the same programs with the blocks mixed by the reflection
# (2/3) J - I on both 3-sides, 2.28) and m (build/bench_fmm_rs_r363m: mixed by the rotations of a numerical minimizer,
# 2.24).  Errors against the exact product (FMM_EXACT), four random instances (FMM_SEED), two at 13824; plans by name
# (no calibration is read or written: FMM_CALIB_DIR is an empty scratch directory).
# Build first: make build/bench_fmm build/bench_fmm_rs_r363h build/bench_fmm_rs_r363m
# Output: results/r363_points_2026-11-22.txt
cd "$(dirname "$0")" || exit 1
SP=${R363_SCRATCH:?set R363_SCRATCH to a scratch directory for the reference cache}
mkdir -p "$SP/ref" "$SP/calib"
unset FMM_INPUT FMM_PRESCALE
export FMM_EXACT=1 FMM_REFCACHE=$SP/ref FMM_CALIB_DIR=$SP/calib
typeset -A BIN; BIN=(dps bench_fmm h bench_fmm_rs_r363h m bench_fmm_rs_r363m)
echo "# the R363 level: dps (DPS's point) / h (mixed by the reflection (2/3) J - I) / m (mixed by a minimizer's rotations); $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
run() {   # n precision rounds seed methods
  for v in dps h m; do
    echo "### $v n=$1 $2 seed=$4  $(date '+%H:%M')"
    FMM_SEED=$4 timeout 900 ./build/$BIN[$v] -n $1 -t $2 -r $3 -m $5 | grep -v '^#   '
  done
}
for seed in 0 1 2 3; do
  echo "## seed=$seed"
  run 3456 f 5 $seed classical,plan=R363/G6
  run 3456 d 5 $seed classical,plan=R363/G6,plan=SW+4/R363/G6
  run 6912 f 3 $seed classical,plan=R363/G,plan=R363+4/R633/G6,plan=R363+4/D48/G6
  run 6912 d 3 $seed classical,plan=R363/G,plan=R363+2/R336/G6,plan=R363+3/R633/G6
done
for seed in 0 1; do
  echo "## 13824, seed=$seed"
  run 13824 f 2 $seed classical,plan=R363/G,plan=R363+3/R336/G6,plan=R363+4/R363/G6
  run 13824 d 2 $seed classical,plan=R363/G,plan=R363+4/R336/G3
done
echo "# top CPU users after the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
echo "# done $(date '+%H:%M')"
