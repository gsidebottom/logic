#!/bin/bash
# f64 errors against the exact (compensated, double-double) product for the matched-time pairs of
# the mixed-levels report: the planner's 3x3x6-family plans against the best accurate_262-only
# plans at the same time, single levels and pipelined plans, at 6912 and 13824; three interleaved
# rounds.  relerr (the difference from Accelerate's dgemm) understates nothing and overstates
# everything in f64, since dgemm's own error is the same size as the plans' (8192: dgemm 7.65e-15,
# D48/G 5.18e-15 exact but 8.72e-15 against dgemm), so only err64 is comparable.
# results/f64exact_2026-10-28.txt
cd "$(dirname "$0")" || exit 1
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
export FMM_EXACT=1 FMM_REFCACHE=$SP/refcache_f64exact
mkdir -p "$FMM_REFCACHE"
echo "# f64 exact-error comparison of the mixed-levels report's matched-time pairs; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
echo "## n=6912 f64  $(date '+%H:%M')"
./build/bench_fmm -n 6912 -t d -r 3 -m classical,plan=D48/G,plan=R336/G,plan=R363/G,plan=R633/G,plan=D48+4/D48/G6,plan=SW+3/D48/G6,plan=R363+4/D48/G6,plan=R363+3/R633/G6,plan=SW/D48+2/D48/G6 | grep -v '^#   '
echo "## n=13824 f64  $(date '+%H:%M')"
./build/bench_fmm -n 13824 -t d -r 3 -m classical,plan=D48/G,plan=R336/G,plan=R363/G,plan=D48+4/D48/G6,plan=R363+3/D48/G6,plan=SW/D48+2/D48/G6,plan=SW/R363+3/R633/G6,plan=R336/R363/G,plan=SW/D48/G | grep -v '^#   '
echo "# done $(date '+%H:%M')"
