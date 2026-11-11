#!/bin/zsh
# Stored as run on 2026-11-11 from the session scratch directory (kres/deep/p10.zsh): the scratch paths are kept;
# see matmul/session_data/README.md.  kres_fast4 is commit 8df5b76's build.
# Resume of p9.zsh after the disk filled at 08:17 (2026-11-11): same chunks, skipping chunks whose kres log shows a
# completed run (a "c <seconds> s" line and no panic).  Output and logs keep the P9_ names; driver log p10.log.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
K=$S/kres/build/kres_fast4; D=$S/kres/deep; LOG=$D/p10.log
echo "=== P10 start $(date '+%Y-%m-%d %H:%M:%S')" >> "$LOG"
for c in ref47 proj47_5 at47 projkm47_7; do
  IN=$D/P7_${c}_open2.txt
  if [[ $(find "$D" -name "P9_${c}_in_*" | wc -l | tr -d ' ') -eq 0 ]]; then split -l 500 "$IN" "$D/P9_${c}_in_"; fi
  echo "--- $c depth 3 on $(wc -l < "$IN" | tr -d ' ') lines in $(find "$D" -name "P9_${c}_in_*" | wc -l | tr -d ' ') chunks $(date '+%H:%M:%S')" >> "$LOG"
  for f in $(find "$D" -name "P9_${c}_in_*" | sort); do
    t=${f##*_in_}; L=$D/P9_${c}_out_${t}.log
    if [[ -f "$L" ]] && grep -qE '^c [0-9.]+ s' "$L" && ! grep -q panicked "$L"; then
      echo "    ${t} done before: $(grep -E '^c k=' "$L" | tr '\n' ';')" >> "$LOG"; continue
    fi
    nice -n 15 /opt/homebrew/bin/timeout 3600s "$K" 4 4 4 "$S/wp/reps/$c.bits" --lines "$f" --mode alt --maxdelta-alt 3 --threads 12 --out "$D/P9_${c}_out_${t}.txt" > "$L" 2>&1
    echo "    ${t} exit $? ; $(grep -E '^c k=' "$L" | tr '\n' ';') $(grep -E '^c [0-9.]+ s' "$L") $(date '+%H:%M:%S')" >> "$LOG"
  done
  echo "    $c written: $(find "$D" -name "P9_${c}_out_*.txt" -exec cat {} + | cut -d' ' -f1 | sort | uniq -c | tr -s ' ' | tr '\n' ' ')" >> "$LOG"
done
echo "=== P10 done $(date '+%Y-%m-%d %H:%M:%S')" >> "$LOG"
