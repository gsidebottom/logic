#!/bin/zsh
# orbit x PLinOpt product sweep — best_for copied VERBATIM from the
# checker-gated final protocol (run_plinopt3.sh).
# Usage: orbit_sweep.sh [N] [REPS] [SEED]
set -u
cd "$(dirname $0)"
P=plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/stack/lib
N=${1:-40}; REPS=${2:-6}; SEED=${3:-11}
[ -d orbit ] && ls orbit | grep -q "sw$(printf %02d $SEED)" || python3 sandwich48.py . orbit $N $SEED
best_for() {
  local f=$1 best=999999 ba=0 bm=0
  for r in $(seq 1 $REPS); do
    for mode in d k kc; do
      case $mode in
        d)  $P/optimizer "$f" > /tmp/orb.slp 2>/dev/null ;;
        k)  $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer > /tmp/orb.slp 2>/dev/null ;;
        kc) $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer 2>/dev/null | $P/compacter -s > /tmp/orb.slp 2>/dev/null ;;
      esac
      [ -s /tmp/orb.slp ] || continue
      local chk=$($P/SLPchecker -M "$f" < /tmp/orb.slp 2>&1 | grep SUCCESS)
      [ -n "$chk" ] || continue
      local nums=$(echo "$chk" | grep -oE "<[0-9]+, [0-9]+>" | tr -d '<>,')
      local t=$(( ${nums%% *} + ${nums##* } ))
      if (( t < best )); then best=$t; ba=${nums%% *}; bm=${nums##* }; fi
    done
  done
  echo "$ba $bm $best"
}
best_total=999999
for d in orbit/sw*/; do
  l=$(best_for ${d}L.sms); r=$(best_for ${d}R.sms); p=$(best_for ${d}P.sms)
  tot=$(( ${l##* } + ${r##* } + ${p##* } ))
  echo "$d L=($l) R=($r) P=($p) TOTAL=$tot"
  if (( tot < best_total )); then
    best_total=$tot
    echo "*** NEW ORBIT BEST $tot ($d) vs published 341 / prior 365 ***"
  fi
done
echo "orbit sweep done: best $best_total (published 341; prior ours 365)"
