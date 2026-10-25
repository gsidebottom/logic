#!/bin/bash
# our 201-operation rank-48 program against the original 315-operation rational scheme
# (PLinOpt's 4x4x4_48_rational), both as fused kernels in the same plans: the two builds
# alternate, three times each
cd "$(dirname "$0")" || exit 1
echo "# 201 vs 315 operations $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
M=dps48,dps48@3,plan=D48+4/D48/G6
for cfg in "8192 f" "8192 d" "16384 f"; do
  set -- $cfg
  for rep in 1 2 3; do
    for b in bench_fmm bench_fmm_orig; do
      echo "## $b n=$1 $2 round $rep"
      ./build/$b -n $1 -t $2 -r 5 -m $M
    done
  done
done
echo "# done $(date '+%H:%M')"
