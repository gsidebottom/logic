#!/bin/zsh
# P1: the reduce-open lines of the overnight k=8..10 sweep, decided exactly by the deficient-case decider
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
K=/Users/greg/projects/logic/target/release/kres; D=$S/kres/deep; N=$S/kres/night; REPS=$S/wp/reps
echo "=== P1 start $(date '+%H:%M:%S')"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  echo "--- $c $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout 3600s "$K" 4 4 4 "$REPS/$c.bits" --lines "$N/${c}_decide_k8-10.txt" --mode reduce --threads 12 --out "$D/P1_$c.txt" | grep -E '^c (k=|[0-9.]+ s|wrote)' | sed 's/^/    /'
  echo "    verdict lines: $(cut -d' ' -f1 "$D/P1_$c.txt" | sort | uniq -c | tr -s ' ' | tr '\n' ';')"
done
echo "=== P1 done $(date '+%H:%M:%S')"
