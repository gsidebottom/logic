#!/bin/bash
# The mixed-levels report's final campaign: the library as it stands (the 2x2 level's programs are DPS's dyadic
# accurate point, Eq. (38) of ISSAC 2024), a fresh calibration, then every measurement the report's tables use,
# in one run on a quiet machine.  (0) state; (1) calibration at 13824, both precisions, exact-product error
# factors (FMM_EXACT), installed for the library; (2) square problems 3456/6912/13824 x f32/f64: the GEMM, the
# planner's picks with the default budget (auto) and without one (auto:none), and the fixed plans the report
# compares, exact errors throughout (err64: f64 product for f32, compensated product for f64); (3) the ternary
# trial, run_t42.sh's protocol; (4) the C library (test_fmm, rectangular cases), the Rust tests, the Rust-vs-C
# crosscheck on the shared cache, and Rust against C alternately.  Output: results/final_campaign_<date>.txt
cd "$(dirname "$0")" || exit 1
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
export FMM_EXACT=1 FMM_REFCACHE=$SP/refcache_f64exact
mkdir -p "$FMM_REFCACHE" "$SP/calib_backup_before_final"
cp -p ~/Library/Caches/fmm/calib5_f32.txt ~/Library/Caches/fmm/calib5_f64.txt results/calib5_f32.txt results/calib5_f64.txt "$SP/calib_backup_before_final/" 2>/dev/null
cp -p results/calib5_f32.txt "$SP/calib_backup_before_final/results_calib5_f32.txt"; cp -p results/calib5_f64.txt "$SP/calib_backup_before_final/results_calib5_f64.txt"
B() { ./build/bench_fmm "$@" | grep -v '^#   [A-Z]'; }
echo "# final campaign of the mixed-levels report; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git -C ../.. rev-parse --short HEAD)"
echo "# kernels: $(grep -m1 '^# kernels' results/calib5_f64.txt)"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
echo "## (1) calibration at 13824 f32  $(date '+%H:%M')"
FMM_RECALIB=1 B -n 13824 -t f -p
echo "## (1) calibration at 13824 f64  $(date '+%H:%M')"
FMM_RECALIB=1 B -n 13824 -t d -p
cp results/calib5_f32.txt results/calib5_f64.txt ~/Library/Caches/fmm/
echo "# installed for the library: $(md5 -q results/calib5_f32.txt) f32, $(md5 -q results/calib5_f64.txt) f64"
grep "^E" results/calib5_f32.txt | tr '\n' ';' | sed 's/^/# f32 error entries: /'; echo; grep "^E" results/calib5_f64.txt | tr '\n' ';' | sed 's/^/# f64 error entries: /'; echo
sq() {  # n precision reps methods
  echo "## (2) square n=$1 $2  $(date '+%H:%M')"; B -n "$1" -t "$2" -r "$3" -m "$4"
}
sq 3456 f 5 classical,auto,auto:none,plan=R363/G6,plan=D48/G6,plan=R336/G6,plan=SW+3/R363/G6
sq 3456 d 5 classical,auto,auto:none,plan=R363/G4,plan=R363/G6,plan=D48/G6,plan=SW+3/R363/G6
sq 6912 f 5 classical,auto,auto:none,plan=D48/G,plan=R336/G,plan=R363/G,plan=D48+4/D48/G6,plan=R363+4/D48/G6,plan=R363+4/R633/G6,plan=SW+4/R363/G6,plan=SW/D48+2/D48/G6
sq 6912 d 3 classical,auto,auto:none,plan=D48/G,plan=R336/G,plan=R363/G,plan=R336/R363/G,plan=D48+4/D48/G6,plan=R363+3/R633/G6,plan=R336+2/R363/G6,plan=R363+4/D48/G6,plan=SW/R363/G6,plan=SW/D48+2/D48/G6
sq 13824 f 3 classical,auto,auto:none,plan=D48/G,plan=R336/G,plan=R363/G,plan=R336/R363/G,plan=D48+4/D48/G6,plan=R363+3/D48/G6,plan=R363+4/R363/G6,plan=R363+4/R336/G6,plan=SW/D48+2/D48/G6
sq 13824 d 3 classical,auto,auto:none,plan=D48/G,plan=R336/G,plan=R363/G,plan=R336/R363/G,plan=D48+4/D48/G6,plan=R363+3/D48/G6,plan=R363+3/R336/G3,plan=R336+3/R363/G3,plan=SW/D48+2/D48/G6,plan=SW/R363+3/R633/G6
echo "## (3) the ternary trial (run_t42.sh's protocol)  $(date '+%H:%M')"
unset FMM_EXACT FMM_REFCACHE
./run_t42.sh
echo "## (4) test_fmm (the C library, rectangular cases)  $(date '+%H:%M')"
./build/test_fmm 2>&1 | grep -v '^#   [A-Z]'
echo "## (4) the Rust tests  $(date '+%H:%M')"
(cd rust && cargo test --release 2>&1 | grep -E "^test |test result|FAILED|panicked" | tail -40)
echo "## (4) crosscheck, Rust against C on the shared cache  $(date '+%H:%M')"
(cd rust && cargo run --release --bin crosscheck 2>&1 | grep -v "^warning\|^ *Compiling\|^ *Finished\|^ *Running\|^ *-->\|^ *|\|^ *=\|^$")
echo "## (4) Rust against C, alternately (run_rust_vs_c.sh)  $(date '+%H:%M')"
./run_rust_vs_c.sh
echo "# top CPU users after the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
echo "# done $(date '+%Y-%m-%d %H:%M')"
