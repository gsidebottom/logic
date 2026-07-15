#!/bin/zsh
# ourslane — machine-score search over OUR scheme's 18 orientation x
# gauge variants (matmul/dps48/ours_sms/). Per variant per round:
# PLinOpt-optimize each side (modes d/k/kc), SLPchecker-gate, then
# rank the variant's best triple by the CALIBRATED machine cost
# (mcscore.py: delayed cycles under measured benchdr constants).
# Reference targets: ours 705.2, accurate 752.8. Improvements land in
# dps48/ourslane/. Kill switch: touch matmul/dps48/STOP_LANES.
set -u
SELF=${0:A}  # absolute path before cd, for xargs self-invocation
cd /Users/greg/projects/logic/matmul/dps48
export DYLD_LIBRARY_PATH=$PWD/stack/lib
PB=plinopt/bin
mkdir -p ourslane
ROUNDS=${ROUNDS:-24}
JOBS=${JOBS:-6}
if [ "${1:-}" = "--variant" ]; then
  variant_round_defined=1  # defined below; dispatch after definitions
fi

variant_round() {
  local V=$1 round=$2
  local dir=ourslane/$V
  mkdir -p $dir
  for S in L R P; do
    for mode in d k kc; do
      local out=$dir/cand_${S}_${mode}.slp
      case $mode in
        d)  $PB/optimizer ours_sms/${V}_${S}.sms > $out 2>/dev/null ;;
        k)  $PB/matrix-transpose ours_sms/${V}_${S}.sms 2>/dev/null \
              | $PB/optimizer -K 2>/dev/null | $PB/transpozer > $out 2>/dev/null ;;
        kc) $PB/matrix-transpose ours_sms/${V}_${S}.sms 2>/dev/null \
              | $PB/optimizer -K 2>/dev/null | $PB/transpozer 2>/dev/null \
              | $PB/compacter -s > $out 2>/dev/null ;;
      esac
      [ -s $out ] || { rm -f $out; continue; }
      $PB/SLPchecker -M ours_sms/${V}_${S}.sms < $out 2>&1 \
        | grep -q SUCCESS || { rm -f $out; continue; }
      # keep the best per side by machine score of (this side + best others)
      if [ ! -f $dir/best_${S}.slp ]; then
        cp $out $dir/best_${S}.slp
      fi
    done
    # pick the candidate minimizing the triple's machine score
    if [ -f $dir/best_L.slp ] && [ -f $dir/best_R.slp ] && [ -f $dir/best_P.slp ]; then
      for c in $dir/cand_${S}_*.slp(N); do
        local cur=$(python3 mcscore.py $dir/best_L.slp $dir/best_R.slp $dir/best_P.slp | awk '{print $1}')
        local l=$dir/best_L.slp r=$dir/best_R.slp p=$dir/best_P.slp
        case $S in L) l=$c;; R) r=$c;; P) p=$c;; esac
        local nw=$(python3 mcscore.py $l $r $p | awk '{print $1}')
        [ "$nw" = "REJECT" ] && continue
        if (( ${nw:-999999} < ${cur:-999999} )); then
          cp $c $dir/best_${S}.slp
          echo "[$V r$round] $S improved: triple machine score $cur -> $nw"
        fi
      done
    fi
  done
  rm -f $dir/cand_*.slp
  if [ -f $dir/best_L.slp ] && [ -f $dir/best_R.slp ] && [ -f $dir/best_P.slp ]; then
    local sc=$(python3 mcscore.py $dir/best_L.slp $dir/best_R.slp $dir/best_P.slp)
    echo "[$V r$round] triple: $sc"
  fi
}

if [ "${1:-}" = "--variant" ]; then
  variant_round "$2" "$3"
  exit 0
fi
echo "=== OURSLANE START $(date): $ROUNDS rounds x 18 variants, $JOBS jobs ==="
echo "targets: ours 705.2 / accurate 752.8 (calibrated delayed cycles)"
for round in $(seq 1 $ROUNDS); do
  [ -f STOP_LANES ] && { echo "STOP_LANES seen"; break; }
  ls ours_sms/*_L.sms | sed 's|ours_sms/||; s|_L\.sms||' \
    | xargs -P $JOBS -I{} "$SELF" --variant {} $round
  # round summary: global best
  best=999999; bv=""
  for V in $(ls ours_sms/*_L.sms | sed 's|ours_sms/||; s|_L\.sms||'); do
    d=ourslane/$V
    [ -f $d/best_L.slp ] && [ -f $d/best_R.slp ] && [ -f $d/best_P.slp ] || continue
    sc=$(python3 mcscore.py $d/best_L.slp $d/best_R.slp $d/best_P.slp | awk '{print int($1)}')
    if (( ${sc:-999999} < best )); then best=$sc; bv=$V; fi
  done
  echo "=== round $round: global best $best ($bv) vs ours 705 / accurate 753 ==="
done
echo "=== OURSLANE DONE $(date) ==="
