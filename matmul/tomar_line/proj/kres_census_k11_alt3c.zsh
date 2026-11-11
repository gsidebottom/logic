#!/bin/zsh
# Stored as run on 2026-11-11 from the session scratch directory (kres/deep/p9.zsh): the scratch paths are kept;
# see matmul/session_data/README.md for where they are now.  kres_fast4 is commit 8df5b76's build.
# Depth-3 pass over the k = 11 alternative lines left open at depth 2, in 500-line chunks: P8 lost at47's 4 h
# of work at its timeout because kres --lines writes its output only at the end.  km47 was decided by P8.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
K=$S/kres/build/kres_fast4; D=$S/kres/deep; LOG=$D/p9.log
echo "=== P9 start $(date '+%Y-%m-%d %H:%M:%S')" >> "$LOG"
for c in ref47 proj47_5 at47 projkm47_7; do
  IN=$D/P7_${c}_open2.txt
  find "$D" -name "P9_${c}_in_*" -delete
  split -l 500 "$IN" "$D/P9_${c}_in_"
  echo "--- $c depth 3 on $(wc -l < "$IN" | tr -d ' ') lines in $(find "$D" -name "P9_${c}_in_*" | wc -l | tr -d ' ') chunks $(date '+%H:%M:%S')" >> "$LOG"
  for f in $(find "$D" -name "P9_${c}_in_*" | sort); do
    t=${f##*_in_}
    nice -n 10 /opt/homebrew/bin/timeout 3600s "$K" 4 4 4 "$S/wp/reps/$c.bits" --lines "$f" --mode alt --maxdelta-alt 3 --threads 12 --out "$D/P9_${c}_out_${t}.txt" > "$D/P9_${c}_out_${t}.log" 2>&1
    echo "    ${t} exit $? ; $(grep -E '^c k=' "$D/P9_${c}_out_${t}.log" | tr '\n' ';') $(grep -E '^c [0-9.]+ s' "$D/P9_${c}_out_${t}.log") $(date '+%H:%M:%S')" >> "$LOG"
  done
  echo "    $c written: $(find "$D" -name "P9_${c}_out_*.txt" -exec cat {} + | cut -d' ' -f1 | sort | uniq -c | tr -s ' ' | tr '\n' ' ')" >> "$LOG"
done
echo "=== P9 done $(date '+%Y-%m-%d %H:%M:%S')" >> "$LOG"
