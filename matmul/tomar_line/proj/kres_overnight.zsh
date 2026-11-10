#!/bin/zsh
# Overnight 2026-11-09/10: the k-subset re-solve pushed out with the Rust decider.
#   A: k = 8..10, five classes, reduce + alt decided on the fly (RED / ALT / undecided lines only);
#   B: SAT on the k = 7 all-three-dependent subsets in alt mode (the exact decider cannot see them), 12-way, two budgets;
#   C: rebuild and class-sort anything A found (RED -> rank 46!, ALT -> new 47s), SAT on A's reduce-undecided lines;
#   D: k = 11 for the five classes while the night lasts (hard cap 06:30 by timeout).
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
L=/Users/greg/projects/logic; P=$L/matmul/tomar_line/proj; K=$L/target/release/kres; REPS=$S/wp/reps; W=$S/kres/night
mkdir -p "$W"
CLASSES=(km47 at47 ref47 proj47_5 projkm47_7)
echo "=== A: k=8..10 decide, start $(date '+%H:%M:%S')"
for c in $CLASSES; do
  echo "--- $c $(date '+%H:%M:%S')"
  /opt/homebrew/bin/timeout 7200s "$K" 4 4 4 "$REPS/$c.bits" --kmin 8 --kmax 10 --threads 12 --both --decide --out "$W/${c}_decide_k8-10.txt" | grep -E '^c k=' | sed 's/^/    /'
  echo "    lines: $(cut -d' ' -f1 "$W/${c}_decide_k8-10.txt" | sort | uniq -c | tr -s ' ' | tr '\n' ';')"
done
echo "=== B: SAT on the k=7 all-dependent subsets, alt mode, start $(date '+%H:%M:%S')"
sat_par() { # mode src outdir class conflicts alts
  local nl per f
  rm -rf "$3.chunks"; mkdir -p "$3.chunks" "$3"
  nl=$(wc -l < "$2" | tr -d ' '); [ "$nl" -eq 0 ] && { echo "    $4 $1: nothing"; return; }
  per=$(( (nl + 11) / 12 )); split -l "$per" -a 2 "$2" "$3.chunks/part_"
  for f in "$3.chunks"/part_*(N); do
    /usr/bin/python3 "$P/kres_solve.py" 4 4 4 "$REPS/$4.bits" "$f" --mode "$1" --out "$3" --tag "$4_$(basename "$f")" --quiet --conflicts "$5" --alts "$6" > "$f.log" 2>&1 &
  done
  wait
  echo "    $4 $1 ($nl, budget $5): $(cat "$3.chunks"/part_*.log | grep -o "'UNSAT': [0-9]*\|'SAT': [0-9]*\|'timeout': [0-9]*\|'same': [0-9]*" | awk -F': ' '{s[$1]+=$2} END {for (k in s) printf "%s %d; ", k, s[k]}') schemes $(ls "$3" | grep -c bits) $(date '+%H:%M:%S')"
  grep -h 'RANK' "$3.chunks"/part_*.log | head -n 3
}
for c in $CLASSES; do
  src=$S/kres/exact/${c}_alt_needs_sat.txt
  [ -f "$src" ] || src=$S/kres/exact/${c}_k3-7.txt
  grep -E '^R k=7 ' "$src" > "$W/${c}_alt7.txt"
  sat_par alt "$W/${c}_alt7.txt" "$W/sat_alt7_$c" "$c" 500000 10
  # retry the timeouts with a ten-times budget: find them by re-solving the whole list would double the work, so the
  # timeouts are recovered from the logs' candidate lines if the solver printed them; kres_solve prints only counts in
  # quiet mode, so a second pass runs on the full list with the big budget only when timeouts occurred
  if cat "$W/sat_alt7_$c.chunks"/part_*.log | grep -q "'timeout': [1-9]"; then
    sat_par alt "$W/${c}_alt7.txt" "$W/sat_alt7b_$c" "$c" 5000000 10
  fi
  for d in "$W/sat_alt7_$c" "$W/sat_alt7b_$c"; do
    if [ -d "$d" ] && [ "$(ls "$d" | grep -c bits)" -gt 0 ]; then
      /usr/bin/python3 "$P/scheme_iso.py" 4 --classes "$REPS" "$d" > "$d.iso.log" 2>&1
      echo "    classes in $(basename "$d"): $(grep -c 'new class representative' "$d.iso.log") (5 known + new)"; grep 'new class representative' "$d.iso.log" | grep -v '/reps/' | sed 's/^/    NEW CLASS: /' | head -n 3
    fi
  done
done
echo "=== C: rebuild A's finds, SAT on its reduce-undecided lines, start $(date '+%H:%M:%S')"
for c in $CLASSES; do
  f=$W/${c}_decide_k8-10.txt
  grep -E '^RED ' "$f" | sed 's/^RED /R /' > "$W/${c}_red.txt"; grep -E '^ALT ' "$f" | sed 's/^ALT /A /' > "$W/${c}_altfound.txt"; grep -E '^R ' "$f" > "$W/${c}_red_undecided.txt"
  echo "    $c: RED $(wc -l < "$W/${c}_red.txt" | tr -d ' '), ALT $(wc -l < "$W/${c}_altfound.txt" | tr -d ' '), reduce-undecided $(wc -l < "$W/${c}_red_undecided.txt" | tr -d ' ')"
  [ -s "$W/${c}_red.txt" ] && /usr/bin/python3 "$P/kres_exact.py" 4 4 4 "$REPS/$c.bits" "$W/${c}_red.txt" --mode reduce --out "$W/rebuild_red_$c" --tag "$c" | tail -n 3
  [ -s "$W/${c}_altfound.txt" ] && { /usr/bin/python3 "$P/kres_exact.py" 4 4 4 "$REPS/$c.bits" "$W/${c}_altfound.txt" --mode alt --out "$W/rebuild_alt_$c" --tag "$c" --quiet | tail -n 1; /usr/bin/python3 "$P/scheme_iso.py" 4 --classes "$REPS" "$W/rebuild_alt_$c" > "$W/rebuild_alt_$c.iso.log" 2>&1; echo "    alt classes: $(grep -c 'new class representative' "$W/rebuild_alt_$c.iso.log") (5 known + new)"; grep 'new class representative' "$W/rebuild_alt_$c.iso.log" | grep -v '/reps/' | sed 's/^/    NEW CLASS: /' | head -n 3; }
  if [ -s "$W/${c}_red_undecided.txt" ]; then
    n=$(wc -l < "$W/${c}_red_undecided.txt" | tr -d ' ')
    if [ "$n" -le 3000 ]; then sat_par reduce "$W/${c}_red_undecided.txt" "$W/sat_red_$c" "$c" 2000000 1; else echo "    $c: $n reduce-undecided lines, too many for SAT tonight (k=9-10 instances take minutes each)"; fi
  fi
done
echo "=== D: k=11 decide while the night lasts (cap 06:30), start $(date '+%H:%M:%S')"
now=$(date '+%s'); stop=$(date -j -f '%Y-%m-%d %H:%M' "$(date -v+1d '+%Y-%m-%d') 06:30" '+%s' 2>/dev/null || echo $(( now + 6 * 3600 )))
for c in $CLASSES; do
  left=$(( stop - $(date '+%s') )); [ "$left" -lt 900 ] && { echo "    out of night for $c"; continue; }
  /opt/homebrew/bin/timeout "${left}s" "$K" 4 4 4 "$REPS/$c.bits" --kmin 11 --kmax 11 --threads 12 --both --decide --out "$W/${c}_decide_k11.txt" | grep -E '^c k=' | sed "s/^/    $c /"
  echo "    $c k=11 lines: $(cut -d' ' -f1 "$W/${c}_decide_k11.txt" 2>/dev/null | sort | uniq -c | tr -s ' ' | tr '\n' ';') $(date '+%H:%M:%S')"
done
echo "=== overnight done $(date '+%H:%M:%S')"
