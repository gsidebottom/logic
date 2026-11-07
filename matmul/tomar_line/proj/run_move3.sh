#!/bin/zsh
# Move 3 A/B: descend from projected seed pools vs from the trivial scheme, equal budget.
# usage: run_move3.sh MINUTES THREADS TAG
set -u
MIN=${1:-5}; THR=${2:-12}; TAG=${3:-m3}
L=/Users/greg/projects/logic
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/move3
B=$L/target/release/flip
TO=$(( MIN * 60 + 90 ))
run() { # name, args...
  local name=$1; shift
  local out=$S/runs/${TAG}_$name
  mkdir -p "$out"
  echo "=== $name start $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout ${TO}s "$B" "$@" --minutes $MIN --threads $THR --seed 7 --out "$out" --lift-below 0 --group-moves 0 > "$out.log" 2>&1
  echo "    exit $? $(tail -n 1 "$out.log")"
}
run 334_triv   3 3 4 --trivial --save-at 30 --write-at 29 --record 29
run 334_proj   3 3 4 --seeds-dir $S/seeds334_all --save-at 30 --write-at 29 --record 29
run 444_triv   4 4 4 --trivial --save-at 49 --write-at 48 --record 47
run 444_proj   4 4 4 --seeds-dir $S/seeds444_from445 --save-at 49 --write-at 48 --record 47
run 344_triv   3 4 4 --trivial --save-at 39 --write-at 38 --record 38
run 344_proj   3 4 4 --seeds-dir $S/seeds344_all --save-at 39 --write-at 38 --record 38
echo "=== move3 done $(date '+%H:%M:%S')"
