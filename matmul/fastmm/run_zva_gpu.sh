#!/bin/zsh
# The library after the changes of 2026-11-14: passes that claim their output lines (DC ZVA), and the
# GPU as a second engine for a level's f32 products (libfmm_gpu.a, bench_fmm_gpu).  On a fresh
# calibration at 13824 (FMM_RECALIB=1 bench_fmm_gpu -n 13824 -t f -p; bench_fmm -n 13824 -t d -p):
# (1) f64, the default build: the GEMM, the planner's pick, the picks of the final campaign of 11-12;
# (2) f32 without the GPU (the default build) and with it (bench_fmm_gpu), and the GPU alone;
# (3) the library's tests, both builds; (4) Rust against C on the shared cache.  Exact errors.
#   ./run_zva_gpu.sh > results/zva_gpu_campaign_2026-11-14.txt
cd ${0:A:h}
SP=${SP:-/private/tmp/claude-501/-Users-greg-projects-logic/3d45768d-4e94-4613-987d-3cadfd01d9af/scratchpad}
export FMM_EXACT=1 FMM_REFCACHE=$SP/refcache
mkdir -p $FMM_REFCACHE
make build/bench_fmm build/bench_fmm_gpu build/libfmm.a build/test_fmm build/libfmm_gpu.a build/test_fmm_gpu build/gpu_gemm >/dev/null || exit 1
B() { ./build/bench_fmm "$@" | grep -v '^#   [A-Z]'; }
G() { ./build/bench_fmm_gpu "$@" | grep -v '^#   [A-Z]'; }
echo "# passes with DC ZVA and GPU-shared leaves; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git -C ../.. rev-parse --short HEAD) + working tree"
echo "# calibration: $(md5 -q results/calib5_f32.txt) f32, $(md5 -q results/calib5_f64.txt) f64, $(md5 -q results/calib5gpu_f32.txt) f32 GPU entries"
echo "## (1) f64  $(date '+%H:%M')"
B -n 3456 -t d -r 5 -m classical,auto,plan=SW+4/R363/G6,plan=R363/G6
B -n 6912 -t d -r 5 -m classical,auto,plan=R363+2/R633/G6,plan=D48+4/D48/G6
B -n 13824 -t d -r 3 -m classical,auto,plan=R363+2/R336/G3,plan=SW/R363+3/R633/G6,plan=D48+4/D48/G6
echo "## (2) f32 without the GPU  $(date '+%H:%M')"
B -n 3456 -t f -r 7 -m classical,auto,plan=R363/G6
B -n 6912 -t f -r 5 -m classical,auto,plan=R363+4/R633/G6
B -n 13824 -t f -r 5 -m classical,auto,plan=R336+2/R363/G6,plan=R363+3/D48/G6
echo "## (2) f32 with the GPU  $(date '+%H:%M')"
for n in 3456 6912 13824; do ./build/gpu_gemm $n 5 graph | head -1; done
G -n 3456 -t f -r 7 -m classical,auto,auto:none,plan=R363/G6M,plan=K32/G6M
G -n 6912 -t f -r 7 -m classical,auto,auto:none,plan=R363/G6M,plan=D48/G6M,plan=K64/G6M
G -n 13824 -t f -r 5 -m classical,auto,auto:none,plan=R363/G6M,plan=R363+4/R336/G6M,plan=R363+6/R336/G6M,plan=K32/GM
unset FMM_EXACT FMM_REFCACHE
echo "## (3) test_fmm, the default build  $(date '+%H:%M')"
FMM_CALIB_DIR=results ./build/test_fmm 2>&1 | grep -v '^#   [A-Z]'
echo "## (3) test_fmm_gpu  $(date '+%H:%M')"
FMM_CALIB_DIR=results ./build/test_fmm_gpu 2>&1 | grep -v '^#   [A-Z]'
echo "## (4) crosscheck, Rust against C (the default build) on the shared cache  $(date '+%H:%M')"
(cd rust && FMM_CALIB_DIR=$PWD/../results cargo run --release --features cbench --bin crosscheck 2>&1 | grep -v "^warning\|^ *Compiling\|^ *Finished\|^ *Running\|^ *-->\|^ *|\|^ *=\|^$")
echo "# done $(date '+%Y-%m-%d %H:%M')"
