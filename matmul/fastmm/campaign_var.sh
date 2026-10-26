#!/bin/bash
# The paper's accuracy campaign and deep recursion for one variant against accurate_262's
# published programs: campaign_var.sh NAME  (programs in matmul/dps48/gamma/slp/NAME_{L,R,P}.slp)
# Output: $SP/camp_NAME.log (main campaign, same format as results/accuracy_campaign_*.txt),
#         $SP/deep_NAME.log (n = 1024, 1-5 levels), $SP/speed_NAME.log
NAME=$1
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
cd /Users/greg/projects/logic/matmul/fastmm || exit 1
make build/bench_fmm_var_$NAME build/bench_fmm_acc262 > $SP/build_$NAME.log 2>&1 || { echo "BUILD FAILED"; tail -5 $SP/build_$NAME.log; exit 1; }
mkdir -p $SP/refcache_$NAME $SP/acc_calib
export FMM_CALIB_DIR=$SP/acc_calib FMM_EXACT=1 FMM_REFCACHE=$SP/refcache_$NAME
D48="classical,dps48,dps48x2,plan=D48/D48/D48/G"
BINS="bench_fmm_acc262 bench_fmm_var_$NAME"
run() {   # precision n dist seed
  local t=$1 n=$2 dist=$3 seed=$4
  for bin in $BINS; do
    echo "## $bin t=$t n=$n dist=$dist seed=$seed"
    FMM_NORMAL=$([ $dist = normal ] && echo 1 || echo 0) FMM_SEED=$seed ./build/$bin -n $n -t $t -r 1 -m "$D48" 2>&1 | grep -E "relerr|reference|rror"
  done
  rm -f $SP/refcache_$NAME/ref_*_${n}_${dist}_${seed}.bin
}
{
echo "# accuracy campaign, $NAME against accurate_262, $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
for n in 4096 8192; do for dist in uniform normal; do for seed in 1 2 3 4 5; do run f $n $dist $seed; done; done; done
for dist in uniform normal; do for seed in 1 2 3 4 5; do run d 4096 $dist $seed; done; done
for dist in uniform normal; do for seed in 1 2 3; do run d 8192 $dist $seed; done; done
echo "# done $(date '+%H:%M')"
} > $SP/camp_$NAME.log 2>&1

# deep recursion at n = 1024, 8 groups at a time
export SP NAME BINS
export D5="classical,dps48,dps48x2,plan=D48/D48/D48/G,plan=D48/D48/D48/D48/G,plan=D48/D48/D48/D48/D48/G"
mkdir -p $SP/deep_parts_$NAME
group() {   # precision dist seed
  local t=$1 dist=$2 seed=$3 n=1024
  local out=$SP/deep_parts_$NAME/${t}_${dist}_${seed}.log
  for bin in $BINS; do
    echo "## $bin t=$t n=$n dist=$dist seed=$seed"
    FMM_NORMAL=$([ $dist = normal ] && echo 1 || echo 0) FMM_SEED=$seed ./build/$bin -n $n -t $t -r 1 -m "$D5" 2>&1 | grep -E "relerr|reference|rror"
  done > $out
  rm -f $SP/refcache_$NAME/ref_*_${n}_${dist}_${seed}.bin
}
export -f group
for t in f d; do for dist in uniform normal; do for seed in 1 2 3 4 5; do echo "$t $dist $seed"; done; done; done | xargs -P 8 -L 1 bash -c 'group "$@"' _
{ echo "# deep recursion $NAME vs accurate_262 $(date '+%Y-%m-%d %H:%M')"; cat $SP/deep_parts_$NAME/*.log; echo "# done $(date '+%H:%M')"; } > $SP/deep_$NAME.log

# speed: alternating rounds of the library's plans
unset FMM_EXACT FMM_REFCACHE
{
echo "# speed $NAME vs accurate_262, alternating rounds, $(date '+%H:%M')"
for round in 1 2 3; do
  for bin in $BINS; do
    for t in f d; do
      echo "## speed $bin round $round $t 4096"; ./build/$bin -n 4096 -t $t -r 5 -m "dps48,plan=D48/G6" | grep -E " min "
      echo "## speed $bin round $round $t 8192"; ./build/$bin -n 8192 -t $t -r 5 -m "dps48,plan=D48+4/D48/G6" | grep -E " min "
    done
  done
done
echo "# done $(date '+%H:%M')"
} > $SP/speed_$NAME.log 2>&1
echo "# campaign_var $NAME done $(date '+%H:%M')"
