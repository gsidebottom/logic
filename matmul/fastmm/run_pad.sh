#!/bin/bash
# sizes that are not powers of two: auto (interpolated calibration, padded when that pays)
# against the classical GEMM and blocked classical; interleaved rounds
cd "$(dirname "$0")" || exit 1
echo "# bench_fmm odd sizes $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
for t in f d; do
  for n in 3000 5000 6000 7000 9000 10000 12000; do ./build/bench_fmm -n $n -t $t -r 5 -m classical,blk2,auto; done
done
echo "# done $(date '+%H:%M')"
