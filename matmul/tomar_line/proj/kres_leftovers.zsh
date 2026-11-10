#!/bin/zsh
# SAT on the exact sweep's leftovers (reduce k=8 with all flattening ranks <= 6; alt on the all-three-dependent subsets,
# k <= 6 fully and a timing sample of k = 7), then the k = 9 reduction candidates by the exact decider.  12-way.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
L=/Users/greg/projects/logic; P=$L/matmul/tomar_line/proj; K=$L/target/release/kres; REPS=$S/wp/reps; W=$S/kres/exact
par() { # mode src outdir tag conflicts alts
  local nl per f
  rm -rf "$3.chunks"; mkdir -p "$3.chunks" "$3"
  nl=$(wc -l < "$2" | tr -d ' '); [ "$nl" -eq 0 ] && { echo "    $4: nothing to do"; return; }
  per=$(( (nl + 11) / 12 )); split -l "$per" -a 2 "$2" "$3.chunks/part_"
  for f in "$3.chunks"/part_*(N); do
    /usr/bin/python3 "$P/kres_solve.py" 4 4 4 "$REPS/$4.bits" "$f" --mode "$1" --out "$3" --tag "$4_$(basename "$f")" --quiet --conflicts "$5" --alts "$6" > "$f.log" 2>&1 &
  done
  wait
  echo "    $4 $1: $(cat "$3.chunks"/part_*.log | grep -o "'UNSAT': [0-9]*\|'SAT': [0-9]*\|'timeout': [0-9]*\|'same': [0-9]*" | awk -F': ' '{s[$1]+=$2} END {for (k in s) printf "%s %d; ", k, s[k]}') schemes $(ls "$3" | grep -c bits) $(date '+%H:%M:%S')"
  grep -h 'RANK' "$3.chunks"/part_*.log | head -n 3
}
echo "=== leftovers start $(date '+%H:%M:%S')"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  par reduce "$W/${c}_reduce_needs_sat.txt" "$W/sat_red_$c" "$c" 2000000 1
done
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  grep -E '^R k=[3456] ' "$W/${c}_alt_needs_sat.txt" > "$W/${c}_alt_sat_k6.txt"
  par alt "$W/${c}_alt_sat_k6.txt" "$W/sat_alt6_$c" "$c" 500000 10
  if [ "$(ls "$W/sat_alt6_$c" | grep -c bits)" -gt 0 ]; then
    /usr/bin/python3 "$P/scheme_iso.py" 4 --classes "$REPS" "$W/sat_alt6_$c" > "$W/iso_sat_alt6_$c.log" 2>&1
    echo "    classes: $(grep -c 'new class representative' "$W/iso_sat_alt6_$c.log") (5 known + new)"; grep 'new class representative' "$W/iso_sat_alt6_$c.log" | grep -v '/reps/' | sed 's/^/    NEW CLASS: /' | head -n 3
  fi
done
echo "=== timing sample: 120 of km47's k=7 all-dependent subsets in alt mode $(date '+%H:%M:%S')"
grep -E '^R k=7 ' "$W/km47_alt_needs_sat.txt" | head -n 120 > "$W/km47_alt7_sample.txt"
par alt "$W/km47_alt7_sample.txt" "$W/sat_alt7_sample_km47" km47 500000 10
echo "=== k=9 reduction candidates, exact decider $(date '+%H:%M:%S')"
for c in km47 at47 ref47 proj47_5 projkm47_7; do
  "$K" 4 4 4 "$REPS/$c.bits" --kmin 9 --kmax 9 --threads 12 --out "$W/${c}_R9.txt" | grep -E '^c k=' | sed "s/^/    $c /"
  rm -rf "$W/chunks_${c}_red9"; mkdir -p "$W/chunks_${c}_red9" "$W/out_${c}_red9"
  nl=$(wc -l < "$W/${c}_R9.txt" | tr -d ' '); per=$(( (nl + 11) / 12 )); [ "$per" -lt 1 ] && per=1
  split -l "$per" -a 2 "$W/${c}_R9.txt" "$W/chunks_${c}_red9/part_"
  for f in "$W/chunks_${c}_red9"/part_*(N); do
    /usr/bin/python3 "$P/kres_exact.py" 4 4 4 "$REPS/$c.bits" "$f" --mode reduce --out "$W/out_${c}_red9" --tag "${c}_$(basename "$f")" --quiet > "$f.log" 2>&1 &
  done
  wait
  echo "    $c k=9 reduce: $(cat "$W/chunks_${c}_red9"/part_*.log | grep -o "'decided_no': [0-9]*\|'reduced': [0-9]*\|'needs_sat': [0-9]*\|'bug': [0-9]*" | awk -F': ' '{s[$1]+=$2} END {for (k in s) printf "%s %d; ", k, s[k]}') schemes $(ls "$W/out_${c}_red9" | grep -c bits) $(date '+%H:%M:%S')"
  grep -h 'RANK' "$W/chunks_${c}_red9"/part_*.log | head -n 3
  rm -f "$W/${c}_R9.txt"
done
echo "=== leftovers done $(date '+%H:%M:%S')"
