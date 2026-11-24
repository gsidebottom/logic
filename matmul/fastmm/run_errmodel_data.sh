#!/bin/zsh
# Data for a position-aware error model (2026-11-23): exact errors (FMM_EXACT: f32 against the f64 product, f64
# against the compensated product) of plans chosen to separate what a level does by where it sits, over several
# random instances (FMM_SEED), without streams or pipelines (they leave the arithmetic unchanged).
#   (g) the GEMM alone by inner dimension k, at 1152 x k x 1152 and square;
#   (1) every level alone; (2) every ordered pair of levels; (3) a selection of three-level plans.
# Sizes 3456 and 6912 (all grids divide them three levels deep); ERRMODEL_SIZES=2304 ERRMODEL_NO_TRIPLES=1 for the
# calibration's size, ERRMODEL_NO_GEMM=1 to skip part (g).  Times are not used.
# Output: results/errmodel_data_<date>.txt.  Build first: make build/bench_fmm
cd "$(dirname "$0")" || exit 1
SP=${ERRMODEL_SCRATCH:?set ERRMODEL_SCRATCH to a scratch directory for the reference cache}
mkdir -p "$SP"
unset FMM_INPUT FMM_PRESCALE
export FMM_EXACT=1 FMM_REFCACHE=$SP
SEEDS=(${=ERRMODEL_SEEDS:-0 1 2 3})
L=(SW D48 R336 R363 R633)
P=()
for a in $L; do P+=($a/G); done
for a in $L; do for b in $L; do P+=($a/$b/G); done; done
[[ -n $ERRMODEL_NO_TRIPLES ]] || \
for p in SW/SW/SW D48/D48/D48 R363/R363/R363 R336/R336/R336 SW/D48/D48 D48/D48/SW SW/R363/R633 R363/R633/SW \
         R363/R336/R633 R336/R363/R633 R633/R363/R336 D48/R363/R336 R363/R336/D48 R363/D48/D48 D48/D48/R363 SW/SW/D48 D48/SW/SW; do
  P+=($p/G)
done
echo "# error-model data; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree; seeds $SEEDS"
[[ -n $ERRMODEL_NO_GEMM ]] || \
for t in f d; do for seed in $SEEDS; do
  for k in 48 96 144 192 288 384 576 768 1152 1728 2304 3456 6912; do
    echo "## gemm 1152x${k}x1152 $t seed=$seed"
    FMM_SEED=$seed ./build/bench_fmm -M 1152 -K $k -N 1152 -t $t -r 1 -m classical | grep -v '^#'
  done
  for n in 96 192 384 768 1536 2304; do
    echo "## gemm square n=$n $t seed=$seed"
    FMM_SEED=$seed ./build/bench_fmm -n $n -t $t -r 1 -m classical | grep -v '^#'
  done
done; done
for n in ${=ERRMODEL_SIZES:-3456 6912}; do for t in f d; do for seed in $SEEDS; do
  echo "## plans n=$n $t seed=$seed  $(date '+%H:%M')"
  for ((i = 1; i <= $#P; i += 12)); do     # the benchmark takes 16 methods at a time
    FMM_SEED=$seed ./build/bench_fmm -n $n -t $t -r 1 -m classical,plan=${(j:,plan=:)P[i,i+11]} | grep -v '^#'
  done
done; done; done
echo "# done $(date '+%H:%M')"
