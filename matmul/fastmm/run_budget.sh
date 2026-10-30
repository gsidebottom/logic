#!/bin/bash
# The default error budget (max_growth 0 = 1, no less accurate than the GEMM) after the error model
# was refit to the exact product with the depth factor: the planner's picks with the default budget
# (auto) and without one (auto:none) against the plans of the report's matched-time comparison, three
# or five interleaved rounds, exact errors (FMM_EXACT; perr is the model's prediction, err64 the
# measurement); then test_fmm and the C-vs-Rust crosscheck (both on the library's cache, which the
# bench's copy is installed into first: the bench calibrates into results/, the library reads
# ~/Library/Caches/fmm).  results/budget_campaign_2026-10-29.txt
cd "$(dirname "$0")" || exit 1
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
export FMM_EXACT=1 FMM_REFCACHE=$SP/refcache_f64exact
echo "# budget campaign: the refit error model (exact product, depth factor) and the default budget 1; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
echo "## n=13824 f32  $(date '+%H:%M')"
./build/bench_fmm -n 13824 -t f -r 3 -m classical,auto,auto:none,plan=D48+4/D48/G6 | grep -v '^#   [A-Z]'
echo "## n=13824 f64  $(date '+%H:%M')"
./build/bench_fmm -n 13824 -t d -r 3 -m classical,auto,auto:none,plan=R363+3/D48/G6,plan=D48+4/D48/G6,plan=R336+3/R363/G3 | grep -v '^#   [A-Z]'
echo "## n=6912 f32  $(date '+%H:%M')"
./build/bench_fmm -n 6912 -t f -r 3 -m classical,auto,auto:none,plan=D48+4/D48/G6 | grep -v '^#   [A-Z]'
echo "## n=6912 f64  $(date '+%H:%M')"
./build/bench_fmm -n 6912 -t d -r 3 -m classical,auto,auto:none,plan=D48+4/D48/G6,plan=R363+3/D48/G6 | grep -v '^#   [A-Z]'
echo "## n=3456 f32  $(date '+%H:%M')"
./build/bench_fmm -n 3456 -t f -r 5 -m classical,auto,auto:none,plan=D48/G6 | grep -v '^#   [A-Z]'
echo "## n=3456 f64  $(date '+%H:%M')"
./build/bench_fmm -n 3456 -t d -r 5 -m classical,auto,auto:none,plan=R363/G6,plan=D48/G6,plan=SW+3/R363/G6 | grep -v '^#   [A-Z]'
unset FMM_EXACT FMM_REFCACHE
echo "## test_fmm  $(date '+%H:%M')"
./build/test_fmm 2>&1 | grep -v '^#   [A-Z]'
echo "## crosscheck (Rust vs C on the shared cache)  $(date '+%H:%M')"
(cd rust && cargo run --release --bin crosscheck 2>&1 | grep -v "^warning\|^ *Compiling\|^ *Finished\|^ *Running\|^ *-->\|^ *|\|^ *=\|^$")
echo "## the bench's cache (results/calib5_*.txt, FMM_CALIB_DIR=results), now with the exact-product error entries, installed for the library"
cp results/calib5_f32.txt results/calib5_f64.txt ~/Library/Caches/fmm/
grep "^E" results/calib5_f32.txt | tr '\n' ';'; echo; grep "^E" results/calib5_f64.txt | tr '\n' ';'; echo
echo "# done $(date '+%H:%M')"
