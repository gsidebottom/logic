#!/bin/zsh
# The position-aware error model (fmm.c, "the accuracy budget"; 2026-11-23) in use:
#   (1) the planner's picks with and without a budget at the report's square sizes, and with the GPU;
#   (2) at each size the pick against the plans it displaced and its nearest competitors, timed (rounds as in the
#       campaign) with errors against the exact product;
#   (3) the model's predictions (perr) for the plans of run_errmodel_data.sh at 3456 and 6912, to set against the
#       errors measured there over four instances (one run each, times not used).
# Build first: make build/bench_fmm build/bench_fmm_gpu.  Output: results/errmodel_picks_<date>.txt
cd "$(dirname "$0")" || exit 1
SP=${ERRMODEL_SCRATCH:?set ERRMODEL_SCRATCH to a scratch directory for the reference cache}
mkdir -p "$SP"
unset FMM_INPUT FMM_PRESCALE FMM_SEED
echo "# the position-aware error model: picks and predictions; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -5 | sed 's/^/#   /'
echo "## (1) picks"
for t in f d; do for n in 1728 3456 6912 13824; do ./build/bench_fmm -n $n -t $t -r 1 -m auto,auto:none | grep '^# auto\|^# error model'; done; done
for n in 3456 6912 13824; do ./build/bench_fmm_gpu -n $n -t f -r 1 -m auto,auto:none | grep '^# auto' | sed 's/$/  (GPU build)/'; done
export FMM_EXACT=1 FMM_REFCACHE=$SP
sq() { echo "## (2) square n=$1 $2  $(date '+%H:%M')"; ./build/bench_fmm -n $1 -t $2 -r $3 -m classical,auto,auto:none,$4 | grep -v '^#   '; }
for round in 1 2; do
  sq 3456 f 5 plan=R363/G6,plan=D48/G6
  sq 3456 d 5 plan=R363/G4,plan=SW+4/R363/G6
  sq 6912 f 5 plan=R363+4/R633/G6,plan=R363+4/D48/G6,plan=D48+4/D48/G6
  sq 6912 d 3 plan=R633+3/R363/G6,plan=R363+2/R336/G6,plan=R336+2/R363/G6,plan=R363+3/R633/G6,plan=D48+4/D48/G6
  sq 13824 f 3 plan=R363+4/R363/G6,plan=R363+3/R336/G6,plan=R336+4/R363/G6,plan=D48+4/D48/G6
  sq 13824 d 3 plan=R363+4/R336/G3,plan=R336+4/R363/G3,plan=SW/R363+3/R633/G6,plan=D48+4/D48/G6
done
unset FMM_EXACT FMM_REFCACHE
L=(SW D48 R336 R363 R633)
P=()
for a in $L; do P+=($a/G); done
for a in $L; do for b in $L; do P+=($a/$b/G); done; done
for p in SW/SW/SW D48/D48/D48 R363/R363/R363 R336/R336/R336 SW/D48/D48 D48/D48/SW SW/R363/R633 R363/R633/SW \
         R363/R336/R633 R336/R363/R633 R633/R363/R336 D48/R363/R336 R363/R336/D48 R363/D48/D48 D48/D48/R363 SW/SW/D48 D48/SW/SW; do
  P+=($p/G)
done
for n in 3456 6912; do for t in f d; do
  echo "## (3) predictions n=$n $t  $(date '+%H:%M')"
  for ((i = 1; i <= $#P; i += 12)); do
    ./build/bench_fmm -n $n -t $t -r 1 -m classical,plan=${(j:,plan=:)P[i,i+11]} | grep -v '^#'
  done
done; done
echo "# top CPU users after the run:"; ps -axo pcpu,pid,etime,comm -r | head -5 | sed 's/^/#   /'
echo "# done $(date '+%H:%M')"
