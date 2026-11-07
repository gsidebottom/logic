#!/bin/zsh
# replicate of the 4x4 pair with another seed and a shorter budget
set -u
MIN=${1:-2}; SEED=${2:-8}; TAG=${3:-m3rep}
L=/Users/greg/projects/logic
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/move3
B=$L/target/release/flip
TO=$(( MIN * 60 + 90 ))
run() { local name=$1; shift; local out=$S/runs/${TAG}_$name; mkdir -p "$out"
  echo "=== $name start $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout ${TO}s "$B" "$@" --minutes $MIN --threads 12 --seed $SEED --out "$out" --lift-below 0 --group-moves 0 > "$out.log" 2>&1
  echo "    exit $? $(tail -n 1 "$out.log")"; }
run 444_triv 4 4 4 --trivial --save-at 49 --write-at 48 --record 47
run 444_proj 4 4 4 --seeds-dir $S/seeds444_from445 --save-at 49 --write-at 48 --record 47
echo "=== rep done $(date '+%H:%M:%S')"
