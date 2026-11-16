#!/bin/bash
# The Rust-vs-C crosscheck on the shared cache (results/), both builds: the default one (with DC ZVA in both)
# and the GPU's (Rust --features gpu against libfmm_gpu.a).  Plans, predicted times and results must be identical.
# The FMM_CALIB_DIR of run_rust_zva.sh and the first run_rust_gpu.sh was relative while the crosscheck ran in
# rust/, so their crosschecks found no calibration and compared the classical GEMM only (2026-11-16).
# results/crosscheck_2026-11-16.txt
cd "$(dirname "$0")" || exit 1
export FMM_CALIB_DIR="$PWD/results"
echo "# crosscheck, both builds; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git -C ../.. rev-parse --short HEAD) + working tree; FMM_CALIB_DIR=$FMM_CALIB_DIR"
make build/libfmm.a build/libfmm_gpu.a >/dev/null || exit 1
F='^warning\|^ *Compiling\|^ *Finished\|^ *Running\|^ *-->\|^ *|\|^ *=\|^$'
echo "## the default build  $(date '+%H:%M')"
(cd rust && cargo run --release --features cbench --bin crosscheck 1000 2048 3000 3456 4096 5000 6912 8192 9000 13824 2>&1 | grep -v "$F")
echo "## with the GPU  $(date '+%H:%M')"
(cd rust && cargo run --release --features cbench,gpu --bin crosscheck 1000 2048 3000 3456 4096 5000 6912 8192 9000 13824 2>&1 | grep -v "$F")
echo "# done $(date '+%H:%M')"
