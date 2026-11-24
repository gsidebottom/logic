#!/bin/zsh
# After the position-aware error model (2026-11-23) the planner's default plan changed at 6912 f64
# (R633+3/R363/G6) and 13824 f32 (R363+4/R363/G6), with the GPU at 13824 (R363/GM), and at some of the sizes and
# shapes of the library's tests.  The rows of the measurements outside the campaign that quote those default
# plans, again, in the formats of their own scripts (run_essl_gemms.sh, run_prescale_timing.sh,
# run_scaled_inputs.sh), then the GPU pick, Rust against C and the crosscheck.  Timed steps first.
# Output: results/<name>_errmodel_<date>.txt, results/errmodel_reruns_<date>.log
cd "$(dirname "$0")" || exit 1
SP=${ERRMODEL_SCRATCH:?set ERRMODEL_SCRATCH to a scratch directory for the reference caches}
mkdir -p "$SP/essl" "$SP/main"
D=$(date '+%Y-%m-%d')
LOG=results/errmodel_reruns_$D.log
head() { echo "# $1; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"; echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | command head -5 | sed 's/^/#   /'; }
note() { echo "$(date '+%H:%M') $1" >> $LOG; }
echo "# reruns for the default plans of the position-aware error model; $(date '+%Y-%m-%d %H:%M')" > $LOG
unset FMM_INPUT FMM_PRESCALE FMM_SEED FMM_EXACT FMM_REFCACHE
M=classical,auto,gemms:1,gemms:2,gemms:3,gemms:4
note "start essl"
{ head "ESSL _GEMMS baseline, the rows whose default plan changed"
  for n t r in 6912 d 5 13824 f 3; do
    echo "## n=$n $t uniform  $(date '+%H:%M')"
    FMM_EXACT=1 FMM_REFCACHE=$SP/essl ./build/bench_fmm -n $n -t $t -r $r -m $M | grep -v '^#   '
  done; } > results/essl_gemms_errmodel_$D.txt 2>&1
note "start prescale"
{ head "prescale timing, the sizes whose default plan changed"
  for n t r in 6912 d 7 13824 f 3; do for round in 1 2; do for p in 0 2 3; do
    echo "## n=$n $t prescale $p round $round  $(date '+%H:%M')"
    FMM_PRESCALE=$p ./build/bench_fmm -n $n -t $t -r $r -m classical,auto | grep -v '^#   '
  done; done; done; } > results/prescale_timing_errmodel_$D.txt 2>&1
note "start gpu"
{ head "the GPU build's pick at 13824 f32"
  for round in 1 2; do
    echo "## gpu n=13824 f round $round  $(date '+%H:%M')"
    FMM_EXACT=1 FMM_REFCACHE=$SP/main ./build/bench_fmm_gpu -n 13824 -t f -r 5 -m classical,auto,auto:none,plan=R363/GM,plan=R363/G6M,plan=R363+4/R336/G6M | grep -v '^#   '
  done; } > results/gpu_errmodel_$D.txt 2>&1
note "start rust_vs_c"
timeout 1500 ./run_rust_vs_c.sh > results/rust_vs_c_errmodel_$D.txt 2>&1
note "start crosscheck"
timeout 900 ./run_crosscheck.sh > results/crosscheck_errmodel_$D.txt 2>&1
note "timed steps done; start essl scaled"
{ for inp in nonneg outer:6 inner:6 cross:6; do for p in 0 1; do
    echo "## n=6912 d input $inp prescale $p  $(date '+%H:%M')"
    FMM_EXACT=1 FMM_INPUT=$inp FMM_PRESCALE=$p ./build/bench_fmm -n 6912 -t d -r 1 -m $M | grep -v '^#   '
  done; done; } >> results/essl_gemms_errmodel_$D.txt 2>&1
note "start scaled"
{ head "scaled inputs, the cases whose default plan changed"
  for inp in uniform nonneg outer:3 outer:6 outerp:6 inner:3 inner:6 innerp:6 cross:3 cross:6 entry:3 entry:6; do for p in 0 1; do
    echo "## n=6912 d input $inp prescale $p  $(date '+%H:%M')"
    FMM_EXACT=1 FMM_INPUT=${inp:#uniform} FMM_PRESCALE=$p ./build/bench_fmm -n 6912 -t d -r 1 -m classical,auto | grep -v '^#   '
  done; done
  for inp in uniform outer:6 inner:6 cross:6 entry:6; do for p in 0 1; do
    echo "## n=13824 f input $inp prescale $p  $(date '+%H:%M')"
    FMM_EXACT=1 FMM_INPUT=${inp:#uniform} FMM_PRESCALE=$p ./build/bench_fmm -n 13824 -t f -r 1 -m classical,auto | grep -v '^#   '
  done; done; } > results/scaled_inputs_errmodel_$D.txt 2>&1
note "done"
