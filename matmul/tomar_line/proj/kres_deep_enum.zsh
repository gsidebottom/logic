#!/bin/zsh
# P3 (2026-11-10): the alternatives question for the all-dependent subsets at k = 8..10 (deficient alt, delta = 1 for
# dims (k-1,k-1,k-1)) by re-enumeration with the extended decider, then k = 11 (reduce + alt) for the five classes.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
K=/Users/greg/projects/logic/target/release/kres; D=$S/kres/deep; REPS=$S/wp/reps
echo "=== P3 start $(date '+%H:%M:%S')"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  echo "--- $c k=8..10 both $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout 10800s "$K" 4 4 4 "$REPS/$c.bits" --kmin 8 --kmax 10 --threads 12 --both --decide --out "$D/P3_${c}_k8-10.txt" | grep -E '^c k=' | sed 's/^/    /'
  echo "    lines: $(cut -d' ' -f1 "$D/P3_${c}_k8-10.txt" | sort | uniq -c | tr -s ' ' | tr '\n' ';')"
done
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  echo "--- $c k=11 both $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout 14400s "$K" 4 4 4 "$REPS/$c.bits" --kmin 11 --kmax 11 --threads 12 --both --decide --out "$D/P3_${c}_k11.txt" | grep -E '^c k=' | sed 's/^/    /'
  echo "    lines: $(cut -d' ' -f1 "$D/P3_${c}_k11.txt" 2>/dev/null | sort | uniq -c | tr -s ' ' | tr '\n' ';')"
done
echo "=== P3 done $(date '+%H:%M:%S')"
