#!/bin/zsh
# What fusing alone is worth: fused 2x2 levels (sw1, sw2rec, sw3rec = SW/G, SW/SW/G, SW/SW/SW/G) against the
# one-operation-at-a-time Strassen-Winograd of gemms_impl.h (gemms:1..3) at the same depth.  Both are the
# <2x2x2:7> class over the same leaf, one multithreaded Accelerate GEMM call per product, so the difference
# is the passes: one fused pass per program against one sweep per addition.  Timing only (no exact
# reference).  Build: make build/bench_fmm.  Output: results/fused_vs_separate_<date>.txt
cd "$(dirname "$0")" || exit 1
unset FMM_INPUT FMM_PRESCALE FMM_EXACT
M=classical,sw1,gemms:1,sw2rec,gemms:2,sw3rec,gemms:3
echo "# fused 2x2 levels against one-at-a-time Strassen-Winograd at equal depth; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
for n r in 8192 5 13824 3; do
  for t in f d; do
    echo "## n=$n $t rounds=$r  $(date '+%H:%M')"
    ./build/bench_fmm -n $n -t $t -r $r -m $M | grep -v '^#   '
  done
done
echo "# top CPU users after the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
echo "# done $(date '+%H:%M')"
