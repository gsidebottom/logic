#!/bin/zsh
# Move 2, round 2: instances between the easy 3x3:23 and the censored <3,3,4>:29 (background priority)
set -u
TO=${1:-600}; PAR=${2:-8}
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/move2
mkdir -p "$S/runs"
jobs=()
for inst in i5_333r22drop0 i5_333r22drop11 i6_234r20 i7_234r19drop0; do for v in none all; do for sd in 1 2; do jobs+=("${inst}_$v $sd"); done; done; done
printf '%s\n' "${jobs[@]}" | xargs -P $PAR -L 1 /bin/zsh -c '
  f=$0; sd=$1
  out='"$S"'/runs/${f}_s${sd}.log
  start=$(date +%s.%N)
  taskpolicy -c background /opt/homebrew/bin/cadical -q -t '"$TO"' --seed=$sd '"$S"'/cnf/$f.cnf > "$out" 2>&1
  end=$(date +%s.%N)
  st=$(grep -m1 "^s " "$out" | cut -d" " -f2); [ -z "$st" ] && st=UNKNOWN
  printf "%-28s seed %s  %-14s %8.2f s\n" "$f" "$sd" "$st" "$(echo "$end - $start" | bc)"
'
echo "=== move2b done $(date '+%H:%M:%S')"
