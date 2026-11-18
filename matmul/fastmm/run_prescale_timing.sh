#!/bin/zsh
# The time prescaling costs: the default plan (auto) and the GEMM without prescaling (mode 0), with
# the library's prescaling as separate passes over copies (2) and folded into the top level's passes
# (3); factors computed inside the timed run in both.  Modes 2 and 3 give bit-identical results
# (FMM_HASH, checked at 1152 on seven plans in both precisions).  Rounds ABCABC against drift.
# Output: results/prescale_timing_<date>.txt.  Build: make build/bench_fmm (the 2026-11-16 run used a
# copy, build/bench_fmm_ps, of the same source and flags, so as not to replace the binary a running
# study was using).  FMM_PRESCALE: 1 the bench's own scaled copies, 2 and 3 the library's paths.
cd "$(dirname "$0")" || exit 1
unset FMM_EXACT FMM_INPUT
echo "# prescale timing; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
for n r in 6912 7 13824 3; do
  for t in f d; do
    for round in 1 2; do
      for p in 0 2 3; do
        echo "## n=$n $t prescale $p round $round  $(date '+%H:%M')"
        FMM_PRESCALE=$p ./build/bench_fmm -n $n -t $t -r $r -m classical,auto | grep -v '^#   '
      done
    done
  done
done
echo "# done $(date '+%H:%M')"
