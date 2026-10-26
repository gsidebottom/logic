#!/bin/zsh
# PLinOpt optimizer sweep (2026-10-26): can more search reach DPS's 262 operations?  Both representations of
# accurate_262 (DPS's data files, our g16s2), L/R/P, several option sets; per-run timeout 120 s.
HERE=$(cd $(dirname $0) && pwd)
P=$HERE/../plinopt/bin
D=$HERE/..
OUT=$1
mkdir -p $OUT
run() {  # name matrixfile options... -> program OUT/name.slp, counts from stderr
  local name=$1 mat=$2; shift 2
  local t0=$(date +%s)
  ( timeout 120 $P/optimizer "$@" $mat | $P/compacter -s > $OUT/$name.slp ) 2> $OUT/$name.err
  local st=$?
  local t1=$(date +%s)
  local add=$(sed 's/\x1b\[[0-9;]*m//g' $OUT/$name.err | grep -E "^# [0-9]+\s+additions" | tail -1 | awk '{print $2}')
  local mul=$(sed 's/\x1b\[[0-9;]*m//g' $OUT/$name.err | grep -E "^# [0-9]+\s+multiplications" | tail -1 | awk '{print $2}')
  echo "$name status $st time $((t1-t0)) s additions $add multiplications $mul"
}
runT() {  # P via transposition: matrix-transpose | optimizer -K opts | transpozer
  local name=$1 mat=$2; shift 2
  local t0=$(date +%s)
  ( $P/matrix-transpose $mat | timeout 120 $P/optimizer -K "$@" | $P/transpozer | $P/compacter -s > $OUT/$name.slp ) 2> $OUT/$name.err
  local st=$?
  local t1=$(date +%s)
  local add=$(sed 's/\x1b\[[0-9;]*m//g' $OUT/$name.err | grep -E "^# [0-9]+\s+additions" | tail -1 | awk '{print $2}')
  local mul=$(sed 's/\x1b\[[0-9;]*m//g' $OUT/$name.err | grep -E "^# [0-9]+\s+multiplications" | tail -1 | awk '{print $2}')
  echo "$name status $st time $((t1-t0)) s additions $add multiplications $mul"
}
echo "# optimizer sweep $(date)"
for rep in dps ours; do
  for M in L R P; do
    if [[ $rep == dps ]]; then mat=$D/plinopt/data/4x4x4_48_accurate_262_$M.sms; else mat=$D/gamma/g16s2_$M.sms; fi
    run ${rep}_${M}_default $mat
    run ${rep}_${M}_O1000 $mat -O 1000
    run ${rep}_${M}_O1000E $mat -O 1000 -E
    run ${rep}_${M}_O1000N $mat -O 1000 -N
    run ${rep}_${M}_O1000A $mat -O 1000 -A
    run ${rep}_${M}_O5000 $mat -O 5000
    if [[ $M == P ]]; then
      runT ${rep}_P_T_default $mat
      runT ${rep}_P_T_O1000 $mat -O 1000
      runT ${rep}_P_T_O5000 $mat -O 5000
    fi
  done
done
echo "# done $(date)"
