#!/bin/bash
# The GPU as a GEMM against the CPU plans: MPSGraph's matrixMultiplication (the fast GPU path),
# MPSMatrixMultiplication, and f16 inputs with an f32 result, at the report's sizes, five rounds
# interleaved with Accelerate's sgemm on the same inputs (gpu_gemm.m); then bench_fmm's exact
# errors at 3456, which the campaigns lack.  results/gpu_gemm_2026-10-28.txt
cd "$(dirname "$0")" || exit 1
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
echo "# GPU GEMM campaign; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); GPU: $(system_profiler SPDisplaysDataType 2>/dev/null | grep -E 'Chipset|Total Number of Cores' | tr -s ' ' | tr '\n' ';')"
for n in 3456 6912 13824; do
  echo "## n=$n  $(date '+%H:%M')"
  for m in graph mps f16; do ./build/gpu_gemm $n 5 $m; done
done
echo "## bench_fmm n=3456 f32 exact errors  $(date '+%H:%M')"
FMM_EXACT=1 ./build/bench_fmm -n 3456 -t f -r 5 -m classical,plan=D48/G6,plan=R363/G6,plan=R336/G6 | grep -v '^#   '
echo "## bench_fmm n=3456 f64 exact errors  $(date '+%H:%M')"
FMM_EXACT=1 FMM_REFCACHE=$SP/refcache_f64exact ./build/bench_fmm -n 3456 -t d -r 5 -m classical,plan=D48/G6,plan=R363/G6,plan=SW+3/R363/G6 | grep -v '^#   '
echo "# done $(date '+%H:%M')"
