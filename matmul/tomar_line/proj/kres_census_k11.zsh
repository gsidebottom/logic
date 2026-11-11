#!/bin/zsh
# Stored as run on 2026-11-10 from the session scratch directory (kres/deep/p6.zsh): the scratch paths are kept;
# kres_census is src/bin/kres.rs as committed with this file, kres_fast4 is commit 8df5b76's build.
# P6 (2026-11-10 evening): the k = 11 sweep (reduce + alt, five classes) with the census enumerator kres_census
# (prefix work units, rank-one census lemma, fast walk).  Regressions against the old binary's finished passes, the chain
# stops on any mismatch: km47 at k = 11 (P3_km47_k11), the four other classes at k = 8..10 (P3_<class>_k8-10) before
# their k = 11 pass.  A regression = the same summary counts (time field dropped) and byte-identical output lines.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
K=$S/kres/build/kres_census; D=$S/kres/deep; REPS=$S/wp/reps; LOG=$D/p6.log
same() {   # same OLDSTEM NEWSTEM LABEL
  local a b
  a=$(grep -E '^c k=' "$D/$1.log" | sed 's/; [0-9.]* s$//')
  b=$(grep -E '^c k=' "$D/$2.log" | sed 's/; [0-9.]* s$//')
  if [[ -n "$a" && "$a" == "$b" ]] && cmp -s "$D/$1.txt" "$D/$2.txt"; then
    echo "    REGRESSION $3: counts and all $(wc -l < "$D/$2.txt" | tr -d ' ') lines IDENTICAL to the old binary's pass" >> "$LOG"; return 0
  fi
  echo "    REGRESSION $3: MISMATCH -- chain stopped" >> "$LOG"; echo "=== P6 stopped $(date '+%H:%M:%S')" >> "$LOG"; return 1
}
echo "=== P6 start $(date '+%H:%M:%S')" >> "$LOG"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  if [[ $c != km47 ]]; then
    echo "--- $c k=8..10 both (regression) $(date '+%H:%M:%S')" >> "$LOG"
    /opt/homebrew/bin/timeout 3600s "$K" 4 4 4 "$REPS/$c.bits" --kmin 8 --kmax 10 --threads 12 --both --decide --out "$D/P6_${c}_k8-10.txt" > "$D/P6_${c}_k8-10.log" 2>&1
    echo "    exit $?" >> "$LOG"
    grep -E '^c k=' "$D/P6_${c}_k8-10.log" | sed 's/^/    /' >> "$LOG"
    same "P3_${c}_k8-10" "P6_${c}_k8-10" "$c k=8..10" || exit 1
  fi
  echo "--- $c k=11 both $(date '+%H:%M:%S')" >> "$LOG"
  /opt/homebrew/bin/timeout 14400s "$K" 4 4 4 "$REPS/$c.bits" --kmin 11 --kmax 11 --threads 12 --both --decide --out "$D/P6_${c}_k11.txt" > "$D/P6_${c}_k11.log" 2>&1
  echo "    exit $?" >> "$LOG"
  grep -E '^c (census|k=)' "$D/P6_${c}_k11.log" | sed 's/^/    /' >> "$LOG"
  echo "    lines: $(cut -d' ' -f1 "$D/P6_${c}_k11.txt" 2>/dev/null | sort | uniq -c | tr -s ' ' | tr '\n' ';') $(date '+%H:%M:%S')" >> "$LOG"
  if [[ $c == km47 ]]; then same "P3_km47_k11" "P6_km47_k11" "km47 k=11" || exit 1; fi
done
echo "=== P6 done $(date '+%H:%M:%S')" >> "$LOG"
