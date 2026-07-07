#!/bin/zsh
# converged head-to-head: NREPS all-modes reps per matrix, SLPchecker
# counts only, winning SLP per matrix SAVED for stitching.
set -u
cd "$(dirname $0)"
P=plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/stack/lib
NREPS=${1:-200}
OUT=converged; mkdir -p $OUT
best_for() {  # $1 sms, $2 save-tag
  local f=$1 tag=$2 best=999999 ba=0 bm=0
  for r in $(seq 1 $NREPS); do
    for mode in d k kc; do
      case $mode in
        d)  $P/optimizer "$f" > /tmp/c4.slp 2>/dev/null ;;
        k)  $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer > /tmp/c4.slp 2>/dev/null ;;
        kc) $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer 2>/dev/null | $P/compacter -s > /tmp/c4.slp 2>/dev/null ;;
      esac
      [ -s /tmp/c4.slp ] || continue
      local chk=$($P/SLPchecker -M "$f" < /tmp/c4.slp 2>&1 | grep SUCCESS)
      [ -n "$chk" ] || continue
      local nums=$(echo "$chk" | grep -oE "<[0-9]+, [0-9]+>" | tr -d '<>,')
      local t=$(( ${nums%% *} + ${nums##* } ))
      if (( t < best )); then
        best=$t; ba=${nums%% *}; bm=${nums##* }
        cp /tmp/c4.slp $OUT/${tag}.slp
        echo "  [$tag r$r $mode] $ba+$bm=$t"
      fi
    done
  done
  echo "$tag FINAL: $ba $bm $best"
}
for spec in \
  "their plinopt/data/4x4x4_48_rational" \
  "RtLtPtt ours_sms/Rt_Lt_Ptt_g2" \
  "PtRtL ours_sms/Pt_Rt_L_g2"; do
  name=${spec%% *}; base=${spec##* }
  for tag in L R P; do
    best_for ${base}_${tag}.sms ${name}_${tag}
  done
done
echo "CONVERGED-DONE"
