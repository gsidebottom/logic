#!/bin/zsh
# checker-gated PLinOpt sweep: direct optimizer only, counts taken
# EXCLUSIVELY from SLPchecker's SUCCESS line (<adds, mults>).
set -u
cd "$(dirname $0)"
P=plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/stack/lib
REPS=${1:-20}
best_for() {
  local f=$1 best=999999 ba=0 bm=0
  for r in $(seq 1 $REPS); do
    $P/optimizer "$f" > /tmp/c2.slp 2>/dev/null
    [ -s /tmp/c2.slp ] || continue
    local chk=$($P/SLPchecker -M "$f" < /tmp/c2.slp 2>&1 | grep SUCCESS)
    [ -n "$chk" ] || continue
    local nums=$(echo "$chk" | grep -oE "<[0-9]+, [0-9]+>" | tr -d '<>,')
    local a=${nums%% *} m=${nums##* } t=$((${nums%% *} + ${nums##* }))
    if (( t < best )); then best=$t; ba=$a; bm=$m; fi
  done
  echo "$ba $bm $best"
}
echo "=== control (their L/R/P) ==="
for tag in L R P; do
  echo "their-$tag: $(best_for plinopt/data/4x4x4_48_rational_${tag}.sms)"
done
echo "=== ours ==="
for f in ours_sms/*_L.sms; do
  base=${f%_L.sms}; name=${base##*/}
  l=$(best_for ${base}_L.sms); r=$(best_for ${base}_R.sms); p=$(best_for ${base}_P.sms)
  echo "$name: L=($l) R=($r) P=($p) TOTAL=$(( ${l##* } + ${r##* } + ${p##* } ))"
done
echo "CHECKED-SWEEP-DONE"
