#!/bin/zsh
# final protocol: per matrix, best of {direct, kernel+transpozer,
# kernel+transpozer+compacter} x REPS, counted ONLY by SLPchecker.
set -u
cd "$(dirname $0)"
P=plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/stack/lib
REPS=${1:-20}
best_for() {
  local f=$1 best=999999 ba=0 bm=0
  for r in $(seq 1 $REPS); do
    for mode in d k kc; do
      case $mode in
        d)  $P/optimizer "$f" > /tmp/c3.slp 2>/dev/null ;;
        k)  $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer > /tmp/c3.slp 2>/dev/null ;;
        kc) $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer 2>/dev/null | $P/compacter -s > /tmp/c3.slp 2>/dev/null ;;
      esac
      [ -s /tmp/c3.slp ] || continue
      local chk=$($P/SLPchecker -M "$f" < /tmp/c3.slp 2>&1 | grep SUCCESS)
      [ -n "$chk" ] || continue
      local nums=$(echo "$chk" | grep -oE "<[0-9]+, [0-9]+>" | tr -d '<>,')
      local t=$(( ${nums%% *} + ${nums##* } ))
      if (( t < best )); then best=$t; ba=${nums%% *}; bm=${nums##* }; fi
    done
  done
  echo "$ba $bm $best"
}
echo "=== control (their L/R/P), all modes ==="
for tag in L R P; do
  echo "their-$tag: $(best_for plinopt/data/4x4x4_48_rational_${tag}.sms)"
done
echo "=== our top instances, all modes ==="
for name in Ptt_L_Rt_g2 Rt_Lt_Ptt_g2 Lt_Pt_R_g2 R_Ptt_Lt_g2 L_R_Pt_g2 Pt_Rt_L_g2; do
  base=ours_sms/$name
  l=$(best_for ${base}_L.sms); r=$(best_for ${base}_R.sms); p=$(best_for ${base}_P.sms)
  echo "$name: L=($l) R=($r) P=($p) TOTAL=$(( ${l##* } + ${r##* } + ${p##* } ))"
done
echo "FINAL-PROTOCOL-DONE"
