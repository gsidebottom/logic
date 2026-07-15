#!/bin/zsh
# orbit x PLinOpt product sweep: random sandwich variants (Brent-
# gated, sandwich48.py) each run through the checker-gated
# best-of-modes protocol. Usage: orbit_sweep.sh [N] [REPS] [SEED]
set -u
cd "$(dirname $0)"
P=plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/stack/lib
N=${1:-40}; REPS=${2:-6}; SEED=${3:-11}
python3 sandwich48.py . orbit $N $SEED
best_total=999999
for d in orbit/sw*/; do
  tot=0
  for M in L R P; do
    best=999999
    for r in $(seq 1 $REPS); do
      for mode in d k kc; do
        case $mode in
          d)  out=$($P/optimizer -q $d/$M.sms 2>/dev/null | $P/SLPchecker -M $d/$M.sms 2>/dev/null | grep SUCCESS) ;;
          k)  out=$($P/optimizer -q -K $d/$M.sms 2>/dev/null | $P/transpozer 2>/dev/null | $P/SLPchecker -M $d/$M.sms 2>/dev/null | grep SUCCESS) ;;
          kc) out=$($P/optimizer -q -K $d/$M.sms 2>/dev/null | $P/transpozer 2>/dev/null | $P/compacter -q 2>/dev/null | $P/SLPchecker -M $d/$M.sms 2>/dev/null | grep SUCCESS) ;;
        esac
        [ -n "$out" ] || continue
        a=$(echo $out | sed -E 's/.*: *([0-9]+) *additions.*/\1/')
        m=$(echo $out | sed -E 's/.*, *([0-9]+) *multiplications.*/\1/')
        [ "$a" = "$out" ] && continue
        c=$((a + m))
        [ $c -lt $best ] && best=$c
      done
    done
    tot=$((tot + best))
  done
  echo "$d TOTAL $tot"
  [ $tot -lt $best_total ] && best_total=$tot && echo "*** NEW ORBIT BEST $tot ($d) vs published 341 ***"
done
echo "orbit sweep done: best $best_total (published 341; our prior best 365)"
