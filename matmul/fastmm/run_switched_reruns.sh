#!/bin/zsh
# The measurements outside the campaign (run_final3.sh) that depend on the 2x2 level or on the planner's
# choices, repeated on the library with the 2x2 level at DPS's Q(sqrt 3) point, one after the other:
# the ESSL comparison, fused against one-at-a-time, the cost of prescaling, Rust against C (with the Rust
# pass driver of 2026-11-22), the crosscheck, the Rust tests, and the badly scaled inputs (errors only, last).
# Build first: make build/bench_fmm build/libfmm.a build/test_fmm build/libfmm_gpu.a; cargo build --release in rust/.
# Output: results/<name>_<date>.txt per step, results/switched_reruns_<date>.log for the steps' times.
cd "$(dirname "$0")" || exit 1
D=$(date '+%Y-%m-%d')
LOG=results/switched_reruns_$D.log
step() {   # name seconds command...
  local name=$1 secs=$2; shift 2
  echo "$(date '+%H:%M') start $name" >> $LOG
  timeout $secs "$@" > results/${name}_$D.txt 2>&1
  echo "$(date '+%H:%M') end $name (exit $?)" >> $LOG
}
echo "# reruns on the switched library; $(date '+%Y-%m-%d %H:%M'); logic $(git rev-parse --short HEAD) + working tree" > $LOG
step essl_gemms 2400 ./run_essl_gemms.sh
step fused_vs_separate 900 ./run_fused_vs_separate.sh
step prescale_timing 1200 ./run_prescale_timing.sh
step rust_vs_c 1500 ./run_rust_vs_c.sh
step crosscheck 900 ./run_crosscheck.sh
step rust_tests 900 zsh -c 'cd rust && cargo test --release 2>&1 | grep -v "^ *Compiling\|^ *Finished\|^$"; cargo test --release --features gpu 2>&1 | grep -v "^ *Compiling\|^ *Finished\|^$"'
step scaled_inputs 4500 ./run_scaled_inputs.sh
echo "$(date '+%H:%M') done" >> $LOG
