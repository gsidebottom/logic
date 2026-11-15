#!/bin/bash
# Part (b) of the mixed-levels report's campaign of 2026-11-15, after the planner's tie rule changed (25% instead of
# 10%, no order rule): the picks re-measured on part (a)'s calibration, unchanged, so that the rule is the only
# difference.  Part (a), results/final_campaign_2026-11-15.txt, has the calibration, the ZVA comparison and the
# ternary trial, which the rule does not touch.  Part (a)'s description, for reference:
# passes that claim their output lines
# (DC ZVA), the planner's tie rules, and the GPU as a second engine for a level's f32 products (libfmm_gpu.a,
# bench_fmm_gpu).  One run on a quiet machine: (0) state; (1) calibration at 13824, both precisions, and the GPU
# entries, exact-product error factors (FMM_EXACT), installed for the library; (2) square problems
# 3456/6912/13824 x f32/f64 on the default build: the GEMM, the planner's picks with the default budget (auto) and
# without one (auto:none), and the fixed plans the report compares, exact errors throughout; (2z) the picks with
# and without DC ZVA, alternately; (2g) f32 with the GPU: MPSGraph alone, the GEMM, the planner's picks, the
# 3x3x6 level over shared leaves, and the classical product shared the same way (K32, K64: no scheme, the hardware
# alone); (3) the ternary trial, run_t42.sh's protocol; (4) the C library's tests in both builds, the Rust tests,
# the Rust-vs-C crosscheck on the shared cache, and Rust against C alternately.
# Output: results/final_campaign_<date>.txt
cd "$(dirname "$0")" || exit 1
SP=/private/tmp/claude-501/-Users-greg-projects-logic/3d45768d-4e94-4613-987d-3cadfd01d9af/scratchpad
export FMM_EXACT=1 FMM_REFCACHE=$SP/refcache
mkdir -p "$FMM_REFCACHE" "$SP/calib_backup_before_final2"
cp -p ~/Library/Caches/fmm/calib5*.txt "$SP/calib_backup_before_final2/" 2>/dev/null
for f in results/calib5_f32.txt results/calib5_f64.txt results/calib5gpu_f32.txt; do cp -p $f "$SP/calib_backup_before_final2/results_$(basename $f)"; done
make build/bench_fmm build/bench_fmm_gpu build/libfmm.a build/test_fmm build/libfmm_gpu.a build/test_fmm_gpu build/gpu_gemm >/dev/null || exit 1
B() { ./build/bench_fmm "$@" | grep -v '^#   [A-Z]'; }
G() { ./build/bench_fmm_gpu "$@" | grep -v '^#   [A-Z]'; }
echo "# campaign part (b): the picks after the tie-rule change, on part (a)'s calibration; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git -C ../.. rev-parse --short HEAD)$(git -C ../.. diff --quiet -- . || echo ' + working tree')"
echo "# kernels: $(grep -m1 '^# kernels' results/calib5_f64.txt)"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
# part (a)'s calibration, not recalibrated: the files differ from the installed cache only in entries for the
# rectangular test shapes, which part (a)'s library tests and Rust runs calibrated on demand into each file
echo "# calibration (part (a)'s, unchanged): $(md5 -q results/calib5_f32.txt) f32, $(md5 -q results/calib5_f64.txt) f64, $(md5 -q results/calib5gpu_f32.txt) f32 GPU entries"
sq() {  # n precision reps methods
  echo "## (2) square n=$1 $2  $(date '+%H:%M')"; B -n "$1" -t "$2" -r "$3" -m "$4"
}
sq 3456 f 5 classical,auto,auto:none,plan=R363/G6,plan=D48/G6,plan=R336/G6,plan=SW+3/R363/G6
sq 3456 d 5 classical,auto,auto:none,plan=R363/G3,plan=R363/G4,plan=R363/G6,plan=D48/G6,plan=SW+3/R363/G6,plan=SW+4/R363/G6
sq 6912 f 5 classical,auto,auto:none,plan=D48/G,plan=R336/G,plan=R363/G,plan=D48+4/D48/G6,plan=R363+4/D48/G6,plan=R363+4/R633/G6,plan=SW+4/R363/G6,plan=SW/D48+2/D48/G6
sq 6912 d 3 classical,auto,auto:none,plan=D48/G,plan=R336/G,plan=R363/G,plan=R336/R363/G,plan=D48+4/D48/G6,plan=R363+3/R633/G6,plan=R363+2/R633/G6,plan=R336+2/R363/G6,plan=R363+4/D48/G6,plan=SW/R363/G6,plan=SW/D48+2/D48/G6
sq 13824 f 3 classical,auto,auto:none,plan=D48/G,plan=R336/G,plan=R363/G,plan=R336/R363/G,plan=D48+4/D48/G6,plan=R363+3/D48/G6,plan=R363+4/R363/G6,plan=R363+4/R336/G6,plan=R336+2/R363/G6,plan=SW/D48+2/D48/G6
sq 13824 d 3 classical,auto,auto:none,plan=D48/G,plan=R336/G,plan=R363/G,plan=R336/R363/G,plan=D48+4/D48/G6,plan=R363+3/D48/G6,plan=R363+3/R336/G3,plan=R363+4/R336/G3,plan=R363+2/R336/G3,plan=R336+3/R363/G3,plan=SW/D48+2/D48/G6,plan=SW/R363+3/R633/G6
echo "## (2g) f32 with the GPU  $(date '+%H:%M')"
for n in 3456 6912 13824; do ./build/gpu_gemm $n 5 graph | head -1; done
G -n 3456 -t f -r 7 -m classical,auto,auto:none,plan=R363/G6,plan=R363/G6M,plan=K32/G6M
G -n 6912 -t f -r 7 -m classical,auto,auto:none,plan=R363+4/R633/G6,plan=R363/G6M,plan=D48/G6M,plan=K64/G6M
G -n 13824 -t f -r 5 -m classical,auto,auto:none,plan=R363+4/R363/G6,plan=R363/G6M,plan=R363+4/R336/G6M,plan=R336+4/R363/G6M,plan=K32/GM
echo "## (2g) the same, second round  $(date '+%H:%M')"
for n in 3456 6912 13824; do ./build/gpu_gemm $n 5 graph | head -1; done
G -n 3456 -t f -r 7 -m classical,auto,plan=R363/G6M,plan=K32/G6M
G -n 6912 -t f -r 7 -m classical,auto,plan=R363/G6M,plan=K64/G6M
G -n 13824 -t f -r 5 -m classical,auto,plan=R363/G6M,plan=K32/GM
unset FMM_EXACT FMM_REFCACHE
echo "## (4) test_fmm (the C library, rectangular cases)  $(date '+%H:%M')"
./build/test_fmm 2>&1 | grep -v '^#   [A-Z]'
echo "## (4) test_fmm_gpu (the library with the GPU)  $(date '+%H:%M')"
./build/test_fmm_gpu 2>&1 | grep -v '^#   [A-Z]'
echo "## (4) the Rust tests  $(date '+%H:%M')"
(cd rust && cargo test --release 2>&1 | grep -E "^test |test result|FAILED|panicked" | tail -40)
echo "## (4) crosscheck, Rust against C on the shared cache  $(date '+%H:%M')"
(cd rust && cargo run --release --features cbench --bin crosscheck 2>&1 | grep -v "^warning\|^ *Compiling\|^ *Finished\|^ *Running\|^ *-->\|^ *|\|^ *=\|^$")
echo "## (4) Rust against C, alternately (run_rust_vs_c.sh)  $(date '+%H:%M')"
./run_rust_vs_c.sh
echo "# top CPU users after the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
echo "# done $(date '+%Y-%m-%d %H:%M')"
