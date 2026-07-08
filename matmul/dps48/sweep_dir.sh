#!/bin/zsh
# checker-gated 3-mode sweep over DIR/*_L.sms triples. args: DIR REPS
set -u
cd "$(dirname $0)"
P=$PWD/plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/stack/lib
DIR=$1; REPS=${2:-40}
best_for() {
  local f=$1 best=999999 ba=0 bm=0
  for r in $(seq 1 $REPS); do
    for mode in d k kc; do
      case $mode in
        d)  $P/optimizer "$f" > /tmp/sd.slp 2>/dev/null ;;
        k)  $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer > /tmp/sd.slp 2>/dev/null ;;
        kc) $P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
              | $P/transpozer 2>/dev/null | $P/compacter -s > /tmp/sd.slp 2>/dev/null ;;
      esac
      [ -s /tmp/sd.slp ] || continue
      local chk=$($P/SLPchecker -M "$f" < /tmp/sd.slp 2>&1 | grep SUCCESS)
      [ -n "$chk" ] || continue
      local nums=$(echo "$chk" | grep -oE "<[0-9]+, [0-9]+>" | tr -d '<>,')
      local t=$(( ${nums%% *} + ${nums##* } ))
      if (( t < best )); then best=$t; ba=${nums%% *}; bm=${nums##* }; fi
    done
  done
  echo "$ba $bm $best"
}
for f in $DIR/*_L.sms; do
  base=${f%_L.sms}; name=${base##*/}
  l=$(best_for ${base}_L.sms); r=$(best_for ${base}_R.sms); p=$(best_for ${base}_P.sms)
  echo "$name: L=($l) R=($r) P=($p) TOTAL=$(( ${l##* } + ${r##* } + ${p##* } ))"
done
echo "SWEEP-DIR-DONE"
