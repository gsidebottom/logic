#!/bin/zsh
# reopt_accurate — deep PLinOpt optimizer storm on the 284-record
# accurate triple: 1500 reps x {d, k, kc} per side, checker-gated;
# any side improvement over <84|76|124> total 284 is a new living
# record. Kill switch: touch matmul/dps48/STOP_LANES.
set -u
cd /Users/greg/projects/logic/matmul/dps48
export DYLD_LIBRARY_PATH=$PWD/stack/lib
PB=plinopt/bin
D=plinopt/data
mkdir -p reopt284
side() {
  local S=$1 base=$2 best=$2
  for rep in $(seq 1 1500); do
    [ -f STOP_LANES ] && break
    for mode in d k kc; do
      local out=/tmp/re284_${S}.slp
      case $mode in
        d)  $PB/optimizer $D/4x4x4_48_accurate_${S}.sms > $out 2>/dev/null ;;
        k)  $PB/matrix-transpose $D/4x4x4_48_accurate_${S}.sms 2>/dev/null \
              | $PB/optimizer -K 2>/dev/null | $PB/transpozer > $out 2>/dev/null ;;
        kc) $PB/matrix-transpose $D/4x4x4_48_accurate_${S}.sms 2>/dev/null \
              | $PB/optimizer -K 2>/dev/null | $PB/transpozer 2>/dev/null \
              | $PB/compacter -s > $out 2>/dev/null ;;
      esac
      [ -s $out ] || continue
      local chk=$($PB/SLPchecker -M $D/4x4x4_48_accurate_${S}.sms < $out 2>&1 | grep SUCCESS)
      [ -n "$chk" ] || continue
      local nums=$(echo "$chk" | grep -oE "<[0-9]+, [0-9]+>" | tr -d '<>,')
      local t=$(( ${nums%% *} + ${nums##* } ))
      if (( t < best )); then
        best=$t
        cp $out reopt284/best_${S}.slp
        echo "[${S}] rep $rep/$mode -> $t  *** BELOW SIDE BASE $base ***"
      fi
    done
    (( rep % 100 == 0 )) && echo "[${S}] rep $rep, best $best (base $base)"
  done
  echo "[${S}] done: best $best (base $base)"
}
echo "=== REOPT284 START $(date) — target: any side below 84/76/124 (total 284) ==="
side L 84 &
side R 76 &
side P 124 &
wait
echo "=== REOPT284 DONE $(date) ==="
