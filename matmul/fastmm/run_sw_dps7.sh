#!/bin/bash
# The 2x2 level's programs: DPS's dyadic accurate point (schemes/opt/dps7_*, gen_kernels.py's
# default since 2026-11-02) against Strassen-Winograd's (build/bench_fmm_winograd, --sw winograd),
# the binaries otherwise identical, exact errors throughout (FMM_EXACT).  Phase 1: the level alone
# and recursively, both precisions (the per-level error ratio, and the pass time at equal GEMM
# work).  Phase 2: the new kernels' calibration at 13824 (the plan tables, both precisions) into
# results/calib_dps7/.  Phase 3: the plans with a 2x2 level on top against the default picks, both
# binaries alternating.  The Winograd binary reads the October 29 calibration from
# results/calib_winograd_2026-11-02/ (its kernels key rewritten; the measurements are of those
# kernels).  results/sw_dps7_2026-11-02.txt
cd "$(dirname "$0")" || exit 1
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
export FMM_EXACT=1 FMM_REFCACHE=$SP/refcache_f64exact
mkdir -p results/calib_dps7
new() { FMM_CALIB_DIR=results/calib_dps7 ./build/bench_fmm "$@" | grep -v '^#   [A-Z]'; }
old() { FMM_CALIB_DIR=results/calib_winograd_2026-11-02 ./build/bench_fmm_winograd "$@" | grep -v '^#   [A-Z]'; }
echo "# the 2x2 level: dps7 (DPS's dyadic accurate point, 27 additions + 9 scalings) against winograd (15 additions); $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -5 | sed 's/^/#   /'
for n in 4096 8192; do for t in f d; do
  echo "## phase 1: the level alone and recursively, n=$n $t  $(date '+%H:%M')"
  for round in 1 2; do
    echo "### dps7 round $round"; new -n $n -t $t -r 3 -m classical,sw1,sw2rec,sw3rec,sw4rec,sw2
    echo "### winograd round $round"; old -n $n -t $t -r 3 -m classical,sw1,sw2rec,sw3rec,sw4rec,sw2
  done
done; done
echo "## phase 2: calibration of the dps7 kernels at 13824, f32  $(date '+%H:%M')"
new -n 13824 -t f -p
echo "## phase 2: calibration of the dps7 kernels at 13824, f64  $(date '+%H:%M')"
new -n 13824 -t d -p
echo "## phase 3: plans with a 2x2 level on top against the default picks  $(date '+%H:%M')"
run3() {   # n, precision, reps, methods
  for round in 1 2; do
    echo "### dps7 n=$1 $2 round $round  $(date '+%H:%M')"; new -n "$1" -t "$2" -r "$3" -m "$4"
    echo "### winograd n=$1 $2 round $round  $(date '+%H:%M')"; old -n "$1" -t "$2" -r "$3" -m "$4"
  done
}
run3 13824 d 3 classical,auto,auto:none,plan=SW/R363+3/R633/G6,plan=R363+3/R336/G3
run3 3456 d 5 classical,auto,auto:none,plan=SW+3/R363/G6,plan=R363/G4
run3 6912 d 3 classical,auto,auto:none,plan=R363+3/R633/G6,plan=SW/R363/G6
run3 6912 f 3 classical,auto,auto:none,plan=SW/D48+2/D48/G6,plan=R363+4/D48/G6
run3 13824 f 3 classical,auto,auto:none,plan=SW/D48+2/D48/G6,plan=R363+4/R363/G6
echo "# top CPU users after the run:"; ps -axo pcpu,pid,etime,comm -r | head -5 | sed 's/^/#   /'
echo "# done $(date '+%H:%M')"
