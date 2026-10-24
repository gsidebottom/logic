#!/bin/bash
# hybrids (our 48 level or Strassen^2 on top, Strassen below; two 48 levels) against recursive
# Strassen and the best classical variant, interleaved rounds
cd "$(dirname "$0")" || exit 1
M=classical,blk4,sw2rec,sw3rec,sw2,dps48,dps48sw,sw2sw
echo "# bench_fmm hybrids $(date '+%Y-%m-%d %H:%M')"
for t in f d; do
  ./build/bench_fmm -n 8192 -t $t -m $M -r 5
  ./build/bench_fmm -n 16384 -t $t -m $M,sw4rec,dps48x2 -r 5
done
echo "# done $(date '+%H:%M')"
