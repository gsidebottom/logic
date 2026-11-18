#!/bin/zsh
# Head to head with IBM ESSL's _GEMMS algorithm (gemms_impl.h: Strassen-Winograd, 1-4 levels over
# Accelerate's GEMM, the conventional unfused implementation): time and exact error against the
# GEMM and the planner's default plan (auto).  ESSL picks its depth by an unpublished rule, so every
# depth is measured and the comparison credits it with its best.  Part 1: well-scaled uniform
# inputs at the report's sizes and at powers of two; part 2: accuracy on badly scaled inputs at
# 6912, without and with the bench's power-of-two prescaling (FMM_PRESCALE=1, all methods alike).
# Build: make build/bench_fmm.  Output: results/essl_gemms_<date>.txt
cd "$(dirname "$0")" || exit 1
unset FMM_INPUT FMM_PRESCALE
export FMM_EXACT=1 FMM_REFCACHE=${FMM_REFCACHE:-/private/tmp/claude-501/-Users-greg-projects-logic/3d45768d-4e94-4613-987d-3cadfd01d9af/scratchpad/refcache_essl}
mkdir -p $FMM_REFCACHE
M=classical,auto,gemms:1,gemms:2,gemms:3,gemms:4
echo "# ESSL _GEMMS baseline; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
PART=${1:-12}   # 1, 2 or 12
if [[ $PART == *1* ]]; then
echo "# part 1: uniform inputs"
for n r in 3456 7 4096 7 6912 5 8192 5 13824 3; do
  for t in f d; do
    echo "## n=$n $t uniform  $(date '+%H:%M')"
    ./build/bench_fmm -n $n -t $t -r $r -m $M | grep -v '^#   '
  done
done
fi
if [[ $PART == *2* ]]; then
echo "# part 2: badly scaled inputs at 6912 (accuracy; one timed run)"
for t in f d; do
  for inp in nonneg outer:6 inner:6 cross:6; do
    for p in 0 1; do
      echo "## n=6912 $t input $inp prescale $p  $(date '+%H:%M')"
      FMM_INPUT=$inp FMM_PRESCALE=$p ./build/bench_fmm -n 6912 -t $t -r 1 -m $M | grep -v '^#   '
    done
  done
done
fi
echo "# done $(date '+%H:%M')"
