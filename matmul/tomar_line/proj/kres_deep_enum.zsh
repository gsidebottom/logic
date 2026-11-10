#!/bin/zsh
# P3 (2026-11-10, relaunched 08:45 with the restricted candidate set and unbuffered logs): the alternatives question for
# the all-dependent subsets at k = 8..10 (deficient alt, delta = 1 for dims (k-1,k-1,k-1)) by re-enumeration, then k = 11
# (reduce + alt), five classes.  kres writes its own log per class (Rust stdout is line-buffered), no pipeline.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
K=/Users/greg/projects/logic/target/release/kres; D=$S/kres/deep; REPS=$S/wp/reps
echo "=== P3 start $(date '+%H:%M:%S')"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  echo "--- $c k=8..10 both $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout 14400s "$K" 4 4 4 "$REPS/$c.bits" --kmin 8 --kmax 10 --threads 12 --both --decide --out "$D/P3_${c}_k8-10.txt" > "$D/P3_${c}_k8-10.log" 2>&1
  grep -E '^c k=' "$D/P3_${c}_k8-10.log" | sed 's/^/    /'
  echo "    lines: $(cut -d' ' -f1 "$D/P3_${c}_k8-10.txt" | sort | uniq -c | tr -s ' ' | tr '\n' ';') $(date '+%H:%M:%S')"
done
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  echo "--- $c k=11 both $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout 21600s "$K" 4 4 4 "$REPS/$c.bits" --kmin 11 --kmax 11 --threads 12 --both --decide --out "$D/P3_${c}_k11.txt" > "$D/P3_${c}_k11.log" 2>&1
  grep -E '^c k=' "$D/P3_${c}_k11.log" | sed 's/^/    /'
  echo "    lines: $(cut -d' ' -f1 "$D/P3_${c}_k11.txt" 2>/dev/null | sort | uniq -c | tr -s ' ' | tr '\n' ';') $(date '+%H:%M:%S')"
done
echo "=== P3 done $(date '+%H:%M:%S')"
