#!/bin/bash
# The Rust port's passes with DC ZVA (2026-11-15): the crosscheck against C on the shared cache (plans, predictions,
# results must be identical), then Rust with and without FMM_ZVA against C, alternately, two rounds.
# results/rust_zva_2026-11-15.txt
cd "$(dirname "$0")" || exit 1
export FMM_CALIB_DIR=results
echo "# Rust with DC ZVA vs C; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git -C ../.. rev-parse --short HEAD) + working tree"
echo "## crosscheck  $(date '+%H:%M')"
(cd rust && cargo run --release --features cbench --bin crosscheck 2>&1 | grep -v "^warning\|^ *Compiling\|^ *Finished\|^ *Running\|^ *-->\|^ *|\|^ *=\|^$")
for round in 1 2; do
  echo "## C round $round  $(date '+%H:%M')"; ./build/test_fmm
  echo "## Rust round $round"; ./rust/target/release/fmmbench
  echo "## Rust FMM_ZVA=0 round $round"; FMM_ZVA=0 ./rust/target/release/fmmbench
  echo "## C 16384 round $round"; ./build/test_fmm 16384
  echo "## Rust 16384 round $round"; ./rust/target/release/fmmbench 16384
  echo "## Rust FMM_ZVA=0 16384 round $round"; FMM_ZVA=0 ./rust/target/release/fmmbench 16384
done
echo "# done $(date '+%H:%M')"
