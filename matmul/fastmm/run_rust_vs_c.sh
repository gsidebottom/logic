#!/bin/bash
# the Rust port (rust/, fmmbench) against the C library (test_fmm), both against Accelerate's
# GEMM, both reading the calibration in results/; alternating runs
cd "$(dirname "$0")" || exit 1
export FMM_CALIB_DIR=results
echo "# Rust vs C library $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
for round in 1 2; do
  echo "## C round $round"; ./build/test_fmm
  echo "## Rust round $round"; ./rust/target/release/fmmbench
  echo "## C 16384 round $round"; ./build/test_fmm 16384
  echo "## Rust 16384 round $round"; ./rust/target/release/fmmbench 16384
done
echo "# done $(date '+%H:%M')"
