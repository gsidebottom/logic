#!/bin/bash
# The paper's accuracy campaign, deep recursion and speed rounds for the f64 passes of the f32
# path (FMM_F64PASS=1) against the plain f32 passes, both with accurate_262's published programs
# (build/bench_fmm_acc262).  The runs with the switch on are logged under the pseudo-build name
# bench_fmm_var_f64pass so that summarize_var.py f64pass reads them.
#   campaign_f64pass.sh            logs: $SP/camp_f64pass.log, deep_f64pass.log, speed_f64pass.log
SP=${SP:-/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad}
cd "$(dirname "$0")" || exit 1
make build/bench_fmm_acc262 > $SP/build_f64pass.log 2>&1 || { echo "BUILD FAILED"; tail -5 $SP/build_f64pass.log; exit 1; }
mkdir -p $SP/refcache_f64pass $SP/acc_calib
export FMM_CALIB_DIR=$SP/acc_calib FMM_REFCACHE=$SP/refcache_f64pass
D48="classical,dps48,dps48x2,plan=D48/D48/D48/G"
bins() { echo "bench_fmm_acc262:0 bench_fmm_var_f64pass:1"; }
run() {   # precision n dist seed methods
  local t=$1 n=$2 dist=$3 seed=$4 m=$5
  for bs in $(bins); do
    local label=${bs%%:*} sw=${bs##*:}
    echo "## $label t=$t n=$n dist=$dist seed=$seed"
    FMM_F64PASS=$sw FMM_EXACT=1 FMM_NORMAL=$([ $dist = normal ] && echo 1 || echo 0) FMM_SEED=$seed ./build/bench_fmm_acc262 -n $n -t $t -r 1 -m "$m" 2>&1 | grep -E "relerr|reference|rror"
  done
  rm -f $SP/refcache_f64pass/ref_*_${n}_${dist}_${seed}.bin
}
{
echo "# accuracy campaign, f64 passes (FMM_F64PASS=1) against the f32 passes, accurate_262's programs, $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
for n in 4096 8192; do for dist in uniform normal; do for seed in 1 2 3 4 5; do run f $n $dist $seed "$D48"; done; done; done
echo "# done $(date '+%H:%M')"
} > $SP/camp_f64pass.log 2>&1

# deep recursion at n = 1024, single precision only (the switch acts on the f32 path)
export SP D48
export D5="classical,dps48,dps48x2,plan=D48/D48/D48/G,plan=D48/D48/D48/D48/G,plan=D48/D48/D48/D48/D48/G"
mkdir -p $SP/deep_parts_f64pass
group() {   # dist seed
  local dist=$1 seed=$2 n=1024 t=f
  local out=$SP/deep_parts_f64pass/${t}_${dist}_${seed}.log
  for bs in "bench_fmm_acc262:0" "bench_fmm_var_f64pass:1"; do
    local label=${bs%%:*} sw=${bs##*:}
    echo "## $label t=$t n=$n dist=$dist seed=$seed"
    FMM_F64PASS=$sw FMM_EXACT=1 FMM_NORMAL=$([ $dist = normal ] && echo 1 || echo 0) FMM_SEED=$seed ./build/bench_fmm_acc262 -n $n -t $t -r 1 -m "$D5" 2>&1 | grep -E "relerr|reference|rror"
  done > $out
  rm -f $SP/refcache_f64pass/ref_*_${n}_${dist}_${seed}.bin
}
export -f group
for dist in uniform normal; do for seed in 1 2 3 4 5; do echo "$dist $seed"; done; done | xargs -P 8 -L 1 bash -c 'group "$@"' _
{ echo "# deep recursion, f64 passes vs f32 passes, $(date '+%Y-%m-%d %H:%M')"; cat $SP/deep_parts_f64pass/*.log; echo "# done $(date '+%H:%M')"; } > $SP/deep_f64pass.log

# speed: alternating rounds, f32 only
unset FMM_EXACT FMM_REFCACHE
{
echo "# speed, f64 passes vs f32 passes, alternating rounds, $(date '+%H:%M')"
for round in 1 2 3; do
  for bs in "bench_fmm_acc262:0" "bench_fmm_var_f64pass:1"; do
    label=${bs%%:*}; sw=${bs##*:}
    echo "## speed $label round $round f 4096"; FMM_F64PASS=$sw ./build/bench_fmm_acc262 -n 4096 -t f -r 5 -m "dps48,plan=D48/G6" | grep -E " min "
    echo "## speed $label round $round f 8192"; FMM_F64PASS=$sw ./build/bench_fmm_acc262 -n 8192 -t f -r 5 -m "dps48,plan=D48+4/D48/G6" | grep -E " min "
    echo "## speed $label round $round f 16384"; FMM_F64PASS=$sw ./build/bench_fmm_acc262 -n 16384 -t f -r 3 -m "dps48,plan=D48+2/D48/G6" | grep -E " min "
  done
done
echo "# done $(date '+%H:%M')"
} > $SP/speed_f64pass.log 2>&1
echo "# campaign_f64pass done $(date '+%H:%M')"
