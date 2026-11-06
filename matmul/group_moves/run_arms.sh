#!/bin/zsh
# Equal-budget A/B of the subspace re-decomposition moves (move 1).
# usage: run_arms.sh MINUTES THREADS TAG
# arms: 0 = baseline engine, 1 = group reductions, 3 = reductions + plateau shuffles
set -u
MIN=${1:-5}; THR=${2:-12}; TAG=${3:-ab}
L=/Users/greg/projects/logic
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/move1
B=$L/target/release/flip
TO=$(( MIN * 60 + 90 ))
run() { # name, args...
  local name=$1; shift
  local out=$S/runs/${TAG}_$name
  mkdir -p "$out"
  echo "=== $name start $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout ${TO}s "$B" "$@" --minutes $MIN --threads $THR --seed 7 --out "$out" --lift-below 0 > "$out.log" 2>&1
  echo "    exit $? $(grep -c 'worker min rank' "$out.log") min-rank lines; $(tail -n 1 "$out.log")"
}
for ARM in 0 1 3; do
  run t1_triv64_arm$ARM  4 4 4 --trivial --save-at 49 --write-at 48 --record 47 --group-moves $ARM --shuffles 2
done
for ARM in 0 1 3; do
  run t3_triv36_arm$ARM  3 3 4 --trivial --save-at 30 --write-at 29 --record 29 --group-moves $ARM --shuffles 2
done
for ARM in 0 1 3; do
  run t2_str49_arm$ARM  4 4 4 --seed-file $L/matmul/external/strassen2-4x4x49.bits --save-at 49 --write-at 48 --record 47 --group-moves $ARM --shuffles 2
done
echo "=== t1-t3 done $(date "+%H:%M:%S")"
# T4: fixed-rank walk at 47 from the three published rank-47 seeds (appended after T1-T3)
for ARM in 0 1 3; do
  out=$S/runs/${TAG}_t4_walk47_arm$ARM; mkdir -p "$out"
  echo "=== t4_walk47_arm$ARM start $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout ${TO}s "$B" 4 4 4 --walk --seeds-dir $L/matmul/x47/walkseeds --out "$out" --rank 47 --max-excess 2 --hard-excess 5 --kick 20 --group-moves $ARM --shuffles 2 --minutes $MIN --threads $THR --seed 7 > "$out.log" 2>&1
  echo "    exit $? $(tail -n 1 "$out.log")"
done
echo "=== t4 done $(date '+%H:%M:%S')"
