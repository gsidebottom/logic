#!/bin/zsh
# Benchmark + verification of bin/optimizer on the three reference matrices (2026-10-26, the
# optimizer-speed branch of the PLinOpt fork; see results/plinopt_optimizer_speed_2026-10-26.txt).
#   bench.sh LABEL [extra optimizer options]
# Single-threaded, -O 200, best of 3 wall times; every program checked with SLPchecker against its
# matrix; output hashes saved to OUT/LABEL_<matrix>.md5 (bit-identity across commits when a seed
# is fixed with -s and OMP_NUM_THREADS=1).
PL=/Users/greg/projects/logic/matmul/dps48/plinopt
D=/Users/greg/projects/logic/matmul/dps48
OUT=${OUT:-/tmp/plbench}
mkdir -p $OUT
label=$1; shift
export OMP_NUM_THREADS=${OMP_NUM_THREADS:-1}
for mat in $D/plinopt/data/4x4x4_48_accurate_262_L.sms $D/plinopt/data/4x4x4_48_accurate_262_R.sms $D/gamma/g16s2_P.sms; do
  name=$(basename $mat .sms)
  best=999
  for rep in 1 2 3; do
    t0=$(python3 -c 'import time;print(time.time())')
    $PL/bin/optimizer "$@" -O 200 $mat > $OUT/${label}_$name.slp 2> $OUT/${label}_$name.err
    t1=$(python3 -c 'import time;print(time.time())')
    t=$(python3 -c "print(f'{$t1-$t0:.3f}')"); (( t < best )) && best=$t
  done
  ok=$($PL/bin/SLPchecker -M $mat < $OUT/${label}_$name.slp 2>&1 | grep -c SUCCESS)
  ops=$(sed 's/\x1b\[[0-9;]*m//g' $OUT/${label}_$name.err | grep -E "^# [0-9]+\s+(additions|multiplications)" | awk '{printf "%s ", $2}')
  md5=$(md5 -q $OUT/${label}_$name.slp)
  echo "$label $name  time $best s  ops $ops check $ok  md5 $md5"
done
