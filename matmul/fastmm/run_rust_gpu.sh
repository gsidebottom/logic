#!/bin/bash
# The Rust port with the GPU's leaves (2026-11-16): the Rust tests with the feature gpu, the crosscheck
# against the C library's GPU build on the shared cache (plans, predictions and results must be identical),
# then Rust against C, both with the GPU, alternately, two rounds, at the GPU's sizes.
# results/rust_gpu_2026-11-16.txt
cd "$(dirname "$0")" || exit 1
export FMM_CALIB_DIR="$PWD/results"     # absolute: the crosscheck runs in rust/
echo "# Rust with the GPU vs C with the GPU; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git -C ../.. rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
make build/libfmm_gpu.a build/test_fmm_gpu >/dev/null || exit 1
echo "## Rust tests with the GPU  $(date '+%H:%M')"
(cd rust && cargo test --release --features gpu 2>&1 | grep -E "^test |test result|FAILED|panicked" | tail -60)
echo "## crosscheck, Rust against C, both with the GPU  $(date '+%H:%M')"
(cd rust && cargo run --release --features cbench,gpu --bin crosscheck 1000 2048 3000 3456 4096 6912 8192 9000 13824 2>&1 \
   | grep -v "^warning\|^ *Compiling\|^ *Finished\|^ *Running\|^ *-->\|^ *|\|^ *=\|^$")
(cd rust && cargo build --release --features gpu --bin fmmbench 2>&1 | grep -E "^error" )
for round in 1 2; do
  echo "## C with the GPU, round $round  $(date '+%H:%M')"; ./build/test_fmm_gpu 3456 6912 13824
  echo "## Rust with the GPU, round $round  $(date '+%H:%M')"; ./rust/target/release/fmmbench 3456 6912 13824
done
echo "# done $(date '+%H:%M')"
