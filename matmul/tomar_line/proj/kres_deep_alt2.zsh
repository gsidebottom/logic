#!/bin/zsh
# P4 (2026-11-10): decide the alternatives question for the k=8..10 subsets the P3 sweep left open (all three slice
# spaces two or more dimensions short), with the bucketed depth-2 decider; then depth 3 on whatever depth 2 leaves.
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
K=/Users/greg/projects/logic/target/release/kres   # the 13:28 run used the side build scratchpad kres/build/kres_fast2 (this commit's code without the reduction-first pass)
D=$S/kres/deep
LOG=$D/p4.log
echo "=== P4 start $(date '+%H:%M:%S')" >> "$LOG"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  echo "--- $c depth 2 on $(wc -l < "$D/P3_${c}_k8-10.txt") lines $(date '+%H:%M:%S')" >> "$LOG"
  /opt/homebrew/bin/timeout 7200s "$K" 4 4 4 "$S/wp/reps/$c.bits" --lines "$D/P3_${c}_k8-10.txt" --mode alt --maxdelta-alt 2 --threads 12 --out "$D/P4_${c}_alt2.txt" > "$D/P4_${c}_alt2.log" 2>&1
  echo "    exit $? ; $(grep -E '^c k=' "$D/P4_${c}_alt2.log" | tr '\n' ';') $(grep -E '^c [0-9.]+ s' "$D/P4_${c}_alt2.log")" >> "$LOG"
  echo "    written: $(cut -d' ' -f1 "$D/P4_${c}_alt2.txt" 2>/dev/null | sort | uniq -c | tr '\n' ' ')" >> "$LOG"
done
echo "=== P4 depth 2 done $(date '+%H:%M:%S')" >> "$LOG"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  grep '^A ' "$D/P4_${c}_alt2.txt" > "$D/P4_${c}_open2.txt" 2>/dev/null
  n=$(wc -l < "$D/P4_${c}_open2.txt")
  echo "--- $c depth 3 on $n lines left open at depth 2 $(date '+%H:%M:%S')" >> "$LOG"
  if [ "$n" -gt 0 ]; then
    /opt/homebrew/bin/timeout 14400s "$K" 4 4 4 "$S/wp/reps/$c.bits" --lines "$D/P4_${c}_open2.txt" --mode alt --maxdelta-alt 3 --threads 12 --out "$D/P4_${c}_alt3.txt" > "$D/P4_${c}_alt3.log" 2>&1
    echo "    exit $? ; $(grep -E '^c k=' "$D/P4_${c}_alt3.log" | tr '\n' ';') $(grep -E '^c [0-9.]+ s' "$D/P4_${c}_alt3.log")" >> "$LOG"
    echo "    written: $(cut -d' ' -f1 "$D/P4_${c}_alt3.txt" 2>/dev/null | sort | uniq -c | tr '\n' ' ')" >> "$LOG"
  fi
done
echo "=== P4 done $(date '+%H:%M:%S')" >> "$LOG"
