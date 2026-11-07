#!/bin/zsh
# Move 2: CaDiCaL on the completion instances with and without capacity constraints.
# usage: run_move2.sh TIMEOUT PARALLEL
set -u
TO=${1:-600}; PAR=${2:-4}
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/move2
mkdir -p "$S/runs"
jobs=()
for inst in i2_333r23 i1_334r29 i3_334r28drop0; do
  for v in none entries caps all; do for sd in 1 2; do jobs+=("${inst}_$v $sd"); done; done
done
for v in none all; do for sd in 1 2; do jobs+=("i3_334r28drop7_$v $sd"); done; done
for v in none all; do jobs+=("i4_444r47_$v 1"); done
printf '%s\n' "${jobs[@]}" | xargs -P $PAR -L 1 /bin/zsh -c '
  f=$0; sd=$1
  out='"$S"'/runs/${f}_s${sd}.log
  start=$(date +%s.%N)
  /opt/homebrew/bin/cadical -q -t '"$TO"' --seed=$sd '"$S"'/cnf/$f.cnf > "$out" 2>&1
  end=$(date +%s.%N)
  st=$(grep -m1 "^s " "$out" | cut -d" " -f2); [ -z "$st" ] && st=UNKNOWN
  printf "%-28s seed %s  %-14s %8.2f s\n" "$f" "$sd" "$st" "$(echo "$end - $start" | bc)"
'
echo "=== move2 done $(date '+%H:%M:%S')"
