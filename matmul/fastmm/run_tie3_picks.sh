#!/bin/zsh
# The planner's tie window widened from 2% to 3% (PLAN_TIE, 2026-11-23): its picks with and without a budget at the
# report's square sizes, the one pick that changes (3456 f64) measured against the plan it displaces, two alternating
# rounds with errors against the exact product, then the library's tests (the picks at the other sizes and the
# rectangular shapes) and the Rust-vs-C crosscheck.  Build first: make build/bench_fmm build/bench_fmm_gpu
# build/libfmm.a build/test_fmm build/libfmm_gpu.a; cargo build --release in rust/.
# Output: results/tie3_picks_<date>.txt
cd "$(dirname "$0")" || exit 1
SP=${TIE3_SCRATCH:?set TIE3_SCRATCH to a scratch directory for the reference cache}
mkdir -p "$SP"
unset FMM_INPUT FMM_PRESCALE
echo "# the tie window at 3%; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -5 | sed 's/^/#   /'
echo "## picks"
for t in f d; do for n in 1728 3456 6912 13824; do ./build/bench_fmm -n $n -t $t -r 1 -m auto,auto:none | grep '^# auto'; done; done
for n in 3456 6912 13824; do ./build/bench_fmm_gpu -n $n -t f -r 1 -m auto | grep '^# auto' | sed 's/$/  (GPU build)/'; done
export FMM_EXACT=1 FMM_REFCACHE=$SP
for round in 1 2; do
  echo "## 3456 f64 round $round  $(date '+%H:%M')"
  ./build/bench_fmm -n 3456 -t d -r 7 -m classical,auto,auto:none,plan=R363/G4,plan=R363/G3,plan=SW+4/R363/G6,plan=SW+3/R363/G6 | grep -v '^#   '
done
unset FMM_EXACT FMM_REFCACHE
echo "## test_fmm  $(date '+%H:%M')"
./build/test_fmm 2>&1 | grep -v '^#   [A-Z]'
echo "## crosscheck  $(date '+%H:%M')"
./run_crosscheck.sh 2>&1 | grep -v "results identical"
echo "# done $(date '+%H:%M')"
