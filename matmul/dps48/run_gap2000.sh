#!/bin/zsh
# 2000-rep gap test: ours (Rt_Lt_Ptt_g2) vs their instance, all six
# matrices in PARALLEL, SLPchecker-counted only, best SLPs saved.
set -u
cd "$(dirname $0)"
P=$PWD/plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/stack/lib
REPS=${1:-2000}
OUT=$PWD/converged2k; mkdir -p $OUT
one_matrix() {  # $1 sms  $2 tag
  local f=$1 tag=$2 best=999999 ba=0 bm=0 tmp=/tmp/g2k_$tag.slp
  for r in $(seq 1 $REPS); do
    for mode in d k kc; do
      case $mode in
        d)  $P/optimizer "$f" > $tmp 2>/dev/null ;;
        k)  $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer > $tmp 2>/dev/null ;;
        kc) $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer 2>/dev/null | $P/compacter -s > $tmp 2>/dev/null ;;
      esac
      [ -s $tmp ] || continue
      local chk=$($P/SLPchecker -M "$f" < $tmp 2>&1 | grep SUCCESS)
      [ -n "$chk" ] || continue
      local nums=$(echo "$chk" | grep -oE "<[0-9]+, [0-9]+>" | tr -d '<>,')
      local t=$(( ${nums%% *} + ${nums##* } ))
      if (( t < best )); then
        best=$t; ba=${nums%% *}; bm=${nums##* }
        cp $tmp $OUT/$tag.slp
        echo "  [$tag r$r/$REPS $mode] $ba+$bm=$t"
      fi
    done
  done
  echo "$tag FINAL: $ba $bm $best"
}
for spec in \
  "their_L plinopt/data/4x4x4_48_rational_L.sms" \
  "their_R plinopt/data/4x4x4_48_rational_R.sms" \
  "their_P plinopt/data/4x4x4_48_rational_P.sms" \
  "ours_L ours_sms/Rt_Lt_Ptt_g2_L.sms" \
  "ours_R ours_sms/Rt_Lt_Ptt_g2_R.sms" \
  "ours_P ours_sms/Rt_Lt_Ptt_g2_P.sms"; do
  tag=${spec%% *}; f=${spec##* }
  one_matrix $f $tag &
done
wait
echo "GAP2000-DONE"
