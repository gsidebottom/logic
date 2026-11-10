#!/bin/zsh
# Exact k-subset re-solve sweep for the five rank-47 classes: candidates by the corrected enumerator (flattening-rank
# filter), reduce k<=8 and alternatives k<=7 by kres_exact.py (slice spaces), 12-way parallel; SAT leftovers listed;
# alternatives class-sorted.  Waits for option 1b to finish.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
L=/Users/greg/projects/logic; P=$L/matmul/tomar_line/proj; K=$L/target/release/kres; REPS=$S/wp/reps; W=$S/kres/exact
while ps -axo command | grep -q '[o]wn445b/run.zsh'; do sleep 20; done
mkdir -p "$W"
echo "=== exact sweep start $(date '+%H:%M:%S')"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  echo "--- $c candidates $(date '+%H:%M:%S')"
  "$K" 4 4 4 "$REPS/$c.bits" --kmin 3 --kmax 7 --threads 12 --both --out "$W/${c}_k3-7.txt" | grep -E '^c k=' | sed 's/^/    /'
  "$K" 4 4 4 "$REPS/$c.bits" --kmin 8 --kmax 8 --threads 12 --out "$W/${c}_R8.txt" | grep -E '^c k=' | sed 's/^/    /'
  grep '^R' "$W/${c}_k3-7.txt" > "$W/${c}_R.txt"; cat "$W/${c}_R8.txt" >> "$W/${c}_R.txt"
  echo "    reduce candidates k<=8: $(wc -l < "$W/${c}_R.txt" | tr -d ' '); alt candidates k<=7: $(wc -l < "$W/${c}_k3-7.txt" | tr -d ' ')"
  for mode in reduce alt; do
    src=$W/${c}_R.txt; [ "$mode" = alt ] && src=$W/${c}_k3-7.txt
    rm -rf "$W/chunks_${c}_$mode"; mkdir -p "$W/chunks_${c}_$mode" "$W/out_${c}_$mode"
    nl=$(wc -l < "$src" | tr -d ' '); per=$(( (nl + 11) / 12 )); [ "$per" -lt 1 ] && per=1
    split -l "$per" -a 2 "$src" "$W/chunks_${c}_$mode/part_"
    for f in "$W/chunks_${c}_$mode"/part_*(N); do
      /usr/bin/python3 "$P/kres_exact.py" 4 4 4 "$REPS/$c.bits" "$f" --mode "$mode" --out "$W/out_${c}_$mode" --tag "${c}_$(basename "$f")" --quiet > "$f.log" 2>&1 &
    done
    wait
    echo "    $mode: $(cat "$W/chunks_${c}_$mode"/part_*.log | grep -c '^c done') chunks; $(cat "$W/chunks_${c}_$mode"/part_*.log | grep -o "'decided_no': [0-9]*\|'reduced': [0-9]*\|'alts': [0-9]*\|'unique': [0-9]*\|'needs_sat': [0-9]*\|'bug': [0-9]*" | awk -F': ' '{s[$1]+=$2} END {for (k in s) printf "%s %d; ", k, s[k]}') schemes $(ls "$W/out_${c}_$mode" | grep -c bits) $(date '+%H:%M:%S')"
    grep -h 'RANK' "$W/chunks_${c}_$mode"/part_*.log | head -n 3
    cat "$W/out_${c}_$mode"/*_needs_sat.txt > "$W/${c}_${mode}_needs_sat.txt" 2>/dev/null; echo "    needs SAT: $(wc -l < "$W/${c}_${mode}_needs_sat.txt" | tr -d ' ')"
  done
  if [ "$(ls "$W/out_${c}_alt" | grep -c bits)" -gt 0 ]; then
    /usr/bin/python3 "$P/scheme_iso.py" 4 --classes "$REPS" "$W/out_${c}_alt" > "$W/iso_alt_$c.log" 2>&1
    echo "    alt classes: $(grep -c 'new class representative' "$W/iso_alt_$c.log") representatives (5 known + new)"
    grep 'new class representative' "$W/iso_alt_$c.log" | grep -v '/reps/' | sed 's/^/    NEW CLASS: /' | head -n 5
    grep 'same class as' "$W/iso_alt_$c.log" | sed -E 's|.*same class as [^ ]*/reps/([a-z0-9_]+)\.bits.*|\1|' | sort | uniq -c | sed 's/^/    /'
  fi
done
echo "=== exact sweep done $(date '+%H:%M:%S')"
