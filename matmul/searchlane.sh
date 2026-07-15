#!/bin/zsh
# searchlane — zk-op-scheme optimization searches (~6 cores, niced):
#   lanes L/R/P: bpcse (BP-style cancellation-aware CSE) attacking the
#     284-record accurate matrices, seed-swept, every emission
#     SLPchecker-gated; improvements kept in searchlane/.
#   lane reopt: PLinOpt optimizer portfolio (d/k/kc modes) re-run on
#     the accurate triple, checker-gated best-total tracking.
# Kill switch: touch matmul/dps48/STOP_LANES.
set -u
cd /Users/greg/projects/logic/matmul/dps48
export DYLD_LIBRARY_PATH=$PWD/stack/lib
PB=plinopt/bin
D=plinopt/data
BP=/Users/greg/projects/logic/target/release/bpcse
mkdir -p searchlane
# checker-verified <adds+cmuls> total for an SLP vs its matrix; 999999 on reject
chkcount() {
  local mat=$1 slp=$2
  local chk=$($PB/SLPchecker -M "$mat" < "$slp" 2>&1 | grep SUCCESS)
  [ -n "$chk" ] || { echo 999999; return; }
  local nums=$(echo "$chk" | grep -oE "<[0-9]+, [0-9]+>" | tr -d '<>,')
  echo $(( ${nums%% *} + ${nums##* } ))
}

bplane() {
  local S=$1 threads=$2 base
  case $S in L) base=84;; R) base=76;; P) base=124;; esac  # accurate checker counts
  local best=$base
  for seed in $(seq 1 60); do
    [ -f STOP_LANES ] && break
    for extra in "" "--pm1"; do
      local out=searchlane/bp_${S}_s${seed}${extra:+p}.slp
      $BP $D/4x4x4_48_accurate_${S}.sms $out --threads $threads \
        --seed $seed --iters 300 --cands 20000 $extra \
        > /dev/null 2>> searchlane/bp_${S}.err
      local t=$(chkcount $D/4x4x4_48_accurate_${S}.sms $out)
      if (( t < best )); then
        best=$t
        echo "[bp $S] seed $seed${extra:+ pm1} -> $t  *** BELOW ${base} ***"
        cp $out searchlane/best_${S}.slp
      else
        rm -f $out
        echo "[bp $S] seed $seed${extra:+ pm1} -> $t (best $best)"
      fi
    done
  done
  echo "[bp $S] lane done, best $best (accurate side base $base)"
}

reoptlane() {
  local bl=84 br=76 bp=124
  for rep in $(seq 1 400); do
    [ -f STOP_LANES ] && break
    for S in L R P; do
      for mode in d k kc; do
        case $mode in
          d)  $PB/optimizer $D/4x4x4_48_accurate_${S}.sms > /tmp/sl_reopt.slp 2>/dev/null ;;
          k)  $PB/matrix-transpose $D/4x4x4_48_accurate_${S}.sms 2>/dev/null \
                | $PB/optimizer -K 2>/dev/null | $PB/transpozer > /tmp/sl_reopt.slp 2>/dev/null ;;
          kc) $PB/matrix-transpose $D/4x4x4_48_accurate_${S}.sms 2>/dev/null \
                | $PB/optimizer -K 2>/dev/null | $PB/transpozer 2>/dev/null \
                | $PB/compacter -s > /tmp/sl_reopt.slp 2>/dev/null ;;
        esac
        [ -s /tmp/sl_reopt.slp ] || continue
        local t=$(chkcount $D/4x4x4_48_accurate_${S}.sms /tmp/sl_reopt.slp)
        local ref
        case $S in L) ref=$bl;; R) ref=$br;; P) ref=$bp;; esac
        if (( t < ref )); then
          case $S in L) bl=$t;; R) br=$t;; P) bp=$t;; esac
          cp /tmp/sl_reopt.slp searchlane/reopt_best_${S}.slp
          echo "[reopt] rep $rep $S/$mode -> $t *** total now $(( bl + br + bp )) vs 284 ***"
        fi
      done
    done
    (( rep % 25 == 0 )) && echo "[reopt] rep $rep: L=$bl R=$br P=$bp total $(( bl + br + bp ))"
  done
  echo "[reopt] done: L=$bl R=$br P=$bp total $(( bl + br + bp )) (record 284)"
}

echo "=== SEARCHLANE START $(date) ==="
bplane L 2 &
bplane R 1 &
bplane P 2 &
reoptlane &
wait
echo "=== SEARCHLANE DONE $(date) ==="
