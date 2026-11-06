#!/bin/zsh
# T5: fixed-rank walk at 29 for <3,3,4> from AlphaTensor's F2 scheme; arms 0/1/3
set -u
MIN=${1:-5}; THR=${2:-12}; TAG=${3:-t5}
L=/Users/greg/projects/logic
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/move1
A=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/alphatensor
B=$L/target/release/flip
TO=$(( MIN * 60 + 90 ))
for ARM in 0 1 3; do
  out=$S/runs/${TAG}_walk29_arm$ARM; mkdir -p "$out"
  echo "=== t5_walk29_arm$ARM start $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout ${TO}s "$B" 3 3 4 --walk --seeds-dir $A/seeds334 --out "$out" --rank 29 --max-excess 3 --hard-excess 6 --kick 20 --group-moves $ARM --shuffles 2 --minutes $MIN --threads $THR --seed 7 > "$out.log" 2>&1
  echo "    exit $? $(tail -n 1 "$out.log")"
done
echo "=== t5 done $(date '+%H:%M:%S')"
