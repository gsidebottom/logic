#!/bin/zsh
# Stored as run on 2026-11-10 from the session scratch directory (kres/deep/p7.zsh): the scratch paths are kept;
# kres_census is src/bin/kres.rs as committed with this file, kres_fast4 is commit 8df5b76's build.
# P7 (2026-11-10 evening): depth-2 pass over the k = 11 lines the P6 sweep leaves open (reduce to depth 3, alternatives to
# depth 2), all five classes, with commit 8df5b76's kres (kres_fast4, the binary validated for this pass at k <= 10).
# Writes P7_<class>_open2.txt = the lines still open, for the depth-3 pass.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
K=$S/kres/build/kres_fast4; D=$S/kres/deep; LOG=$D/p7.log
echo "=== P7 start $(date '+%H:%M:%S')" >> "$LOG"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  IN=$D/P6_${c}_k11.txt
  if [ ! -s "$IN" ]; then echo "--- $c: no k=11 lines ($IN missing or empty)" >> "$LOG"; continue; fi
  echo "--- $c depth 2 (reduce to depth 3, alt to depth 2) on $(wc -l < "$IN" | tr -d ' ') lines: $(cut -d' ' -f1 "$IN" | sort | uniq -c | tr -s ' ' | tr '\n' ' ') $(date '+%H:%M:%S')" >> "$LOG"
  /opt/homebrew/bin/timeout 7200s "$K" 4 4 4 "$S/wp/reps/$c.bits" --lines "$IN" --mode both --maxdelta 3 --maxdelta-alt 2 --threads 12 --out "$D/P7_${c}_d2.txt" > "$D/P7_${c}_d2.log" 2>&1
  echo "    exit $? ; $(grep -E '^c k=' "$D/P7_${c}_d2.log" | tr '\n' ';') $(grep -E '^c [0-9.]+ s' "$D/P7_${c}_d2.log")" >> "$LOG"
  echo "    written: $(cut -d' ' -f1 "$D/P7_${c}_d2.txt" 2>/dev/null | sort | uniq -c | tr -s ' ' | tr '\n' ' ')" >> "$LOG"
  grep -E '^(A|R) ' "$D/P7_${c}_d2.txt" > "$D/P7_${c}_open2.txt" 2>/dev/null
  echo "    open at depth 2: $(wc -l < "$D/P7_${c}_open2.txt" | tr -d ' ') lines ($(grep -o 'dims=[0-9,]*' "$D/P7_${c}_open2.txt" | sort | uniq -c | sort -rn | head -4 | tr -s ' ' | tr '\n' ' ')) $(date '+%H:%M:%S')" >> "$LOG"
done
echo "=== P7 done $(date '+%H:%M:%S')" >> "$LOG"
