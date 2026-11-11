#!/bin/zsh
# Stored as run on 2026-11-10 from the session scratch directory (kres/deep/p8.zsh): the scratch paths are kept;
# kres_census is src/bin/kres.rs as committed with this file, kres_fast4 is commit 8df5b76's build.
# Depth-3 pass over the k = 11 alternative lines left open at depth 2 (P7_<class>_open2.txt), same binary as P7.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
K=$S/kres/build/kres_fast4; D=$S/kres/deep; LOG=$D/p8.log
echo "=== P8 start $(date '+%H:%M:%S')" >> "$LOG"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  IN=$D/P7_${c}_open2.txt
  n=$(wc -l < "$IN" | tr -d ' ')
  echo "--- $c depth 3 on $n lines left open at depth 2 $(date '+%H:%M:%S')" >> "$LOG"
  if [ "$n" -gt 0 ]; then
    /opt/homebrew/bin/timeout 14400s "$K" 4 4 4 "$S/wp/reps/$c.bits" --lines "$IN" --mode alt --maxdelta-alt 3 --threads 12 --out "$D/P8_${c}_alt3.txt" > "$D/P8_${c}_alt3.log" 2>&1
    echo "    exit $? ; $(grep -E '^c k=' "$D/P8_${c}_alt3.log" | tr '\n' ';') $(grep -E '^c [0-9.]+ s' "$D/P8_${c}_alt3.log")" >> "$LOG"
    echo "    written: $(cut -d' ' -f1 "$D/P8_${c}_alt3.txt" 2>/dev/null | sort | uniq -c | tr -s ' ' | tr '\n' ' ')" >> "$LOG"
  fi
done
echo "=== P8 done $(date '+%H:%M:%S')" >> "$LOG"
