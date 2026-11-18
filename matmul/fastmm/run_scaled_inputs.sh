#!/bin/zsh
# Error on badly scaled inputs: the paper measures max-norm relative error on uniform [-1,1) inputs,
# which cannot see the componentwise error of Strassen-type schemes.  Each case: the classical GEMM,
# the default plan (auto) and single levels of every scheme, error against the exact product as
# err64 (max-norm, the paper's) and cw (max |C - C_exact| / (|A||B|), componentwise), without and
# with power-of-two outside + inside prescaling (FMM_PRESCALE=1).  Inputs: bench_impl.h, FMM_INPUT.
# Output: results/scaled_inputs_<date>.txt
cd "$(dirname "$0")" || exit 1
export FMM_EXACT=1
unset FMM_REFCACHE
echo "# scaled inputs; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
M=classical,auto,plan=SW/G,plan=D48/G,plan=R336/G,plan=R363/G,plan=R633/G,plan=D48/D48/G,plan=R363/R336/G
INPUTS=(uniform nonneg outer:3 outer:6 outerp:6 inner:3 inner:6 innerp:6 cross:3 cross:6 entry:3 entry:6)
for t in f d; do
  for inp in $INPUTS; do
    for p in 0 1; do
      echo "## n=6912 $t input $inp prescale $p  $(date '+%H:%M')"
      FMM_INPUT=${inp:#uniform} FMM_PRESCALE=$p ./build/bench_fmm -n 6912 -t $t -r 1 -m $M | grep -v '^#   '
    done
  done
done
for t in f d; do
  for inp in uniform outer:6 inner:6 cross:6 entry:6; do
    for p in 0 1; do
      echo "## n=13824 $t input $inp prescale $p  $(date '+%H:%M')"
      FMM_INPUT=${inp:#uniform} FMM_PRESCALE=$p ./build/bench_fmm -n 13824 -t $t -r 1 -m classical,auto | grep -v '^#   '
    done
  done
done
echo "# done $(date '+%H:%M')"
