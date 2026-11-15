#!/bin/bash
# What non-dyadic constants cost the <3x3x6:40> level (nondyadic.py): the direct-sum programs (rdirect) against the
# same scheme rescaled per product -- ctl (a = b = 1) and p2 (powers of two) must reproduce rdirect; nd3 (3, 1/3) and
# ndr (random 1/3 .. 3) have non-dyadic constants and the same growth factor.  Errors against the exact reference
# (FMM_EXACT: f32 the f64 product, f64 the double-double product), four random instances, two sizes, both precisions.
# results/nondyadic_2026-11-14.txt
cd "$(dirname "$0")" || exit 1
python3 nondyadic.py > /dev/null
for v in ctl p2 nd3 ndr; do
  mkdir -p build/nd_$v && python3 gen_kernels.py build/nd_$v/kernels.h --rschemes schemes/nd/$v > /dev/null &&
  clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild/nd_$v bench_fmm.c -framework Accelerate -o build/bench_fmm_nd_$v || exit 1
done
make -s build/bench_fmm_rdirect || exit 1
export FMM_EXACT=1 FMM_REFCACHE=${FMM_REFCACHE:-/private/tmp/claude-501/-Users-greg-projects-logic/3d45768d-4e94-4613-987d-3cadfd01d9af/scratchpad/refcache_nd}
mkdir -p "$FMM_REFCACHE"
echo "# non-dyadic constants on the <3x3x6:40> level; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
for n in 3456 6912; do for t in f d; do for seed in 0 1 2 3; do
  for v in rdirect nd_ctl nd_p2 nd_nd3 nd_ndr; do
    echo "## $v n=$n $t seed=$seed  $(date '+%H:%M')"
    FMM_SEED=$seed timeout 900 ./build/bench_fmm_$v -n $n -t $t -r 3 -m classical,plan=R336/G,plan=R363/G,plan=R633/G,plan=R336/R363/G,plan=R363+3/R633/G6 | grep -v '^#   '
  done
done; done; done
echo "# done $(date '+%H:%M')"
