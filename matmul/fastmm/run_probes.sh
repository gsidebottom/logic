#!/bin/bash
# is Accelerate's GEMM bound by the SME units, and what can the idle cores add? (probe_threads),
# then three ways of timing the block GEMMs against their time inside a plan (bench_fmm -G)
cd "$(dirname "$0")" || exit 1
echo "# probes $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
for t in f d; do
  for g in 0 1 2 3 4 5 10; do ./build/probe_threads -t $t -n 2048 -g $g -v 0 -s 3; done
  for v in 1 5 10 14; do ./build/probe_threads -t $t -g -1 -v $v -s 3; done
  for v in 4 8 12; do ./build/probe_threads -t $t -n 2048 -g 0 -v $v -s 3; done
  ./build/probe_threads -t $t -n 2048 -g 2 -v 8 -s 3
done
for t in f d; do ./build/bench_fmm -n 8192 -t $t -G; done
echo "# done $(date '+%H:%M')"
