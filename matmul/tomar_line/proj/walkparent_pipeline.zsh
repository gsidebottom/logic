#!/bin/zsh
# walk-parent pipeline: a fixed-rank walk in <4,4,5> from a parent, capped at NEW distinct schemes; each walked scheme
# projected (col) to 4x4, PER seeds apiece; a DMIN-minute 12-thread descent from the pool; the 47s class-sorted against
# the five known representatives.  usage: pipeline.zsh PARENT_DIR RANK TAG [NEW=300] [WMIN=20] [DMIN=20] [PER=10] [THIN=1]
# (THIN=K writes every K-th new distinct walked scheme, so NEW=30000 THIN=100 keeps 300 schemes spread along the walk)
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/wp
L=/Users/greg/projects/logic; M=$L/matmul; F=$L/target/release/flip
PARENT=$1; RANK=$2; TAG=$3; NEW=${4:-300}; WMIN=${5:-20}; DMIN=${6:-20}; PER=${7:-10}; THIN=${8:-1}
W=$S/$TAG; mkdir -p "$W/walk" "$W/seeds" "$W/d"
export PYTHONHASHSEED=0
echo "=== $TAG walk start $(date '+%H:%M:%S') (parent $PARENT rank $RANK, cap $NEW new, thin $THIN, $WMIN min)"
/opt/homebrew/bin/timeout $(( WMIN * 60 + 120 ))s "$F" 4 4 5 --walk --seeds-dir "$PARENT" --out "$W/walk" --rank "$RANK" --max-excess 2 --hard-excess 4 --kick 20 --minutes "$WMIN" --threads 12 --seed 5 --max-new "$NEW" --thin "$THIN" > "$W/walk.log" 2>&1
echo "    exit $? | $(ls "$W/walk" | wc -l | tr -d ' ') walked schemes | $(grep -E '^c (final|walk)' "$W/walk.log" | tail -n 2 | tr '\n' ' ')"
grep -E 'REACHED IN WALK MODE' "$W/walk.log" | head -n 3
echo "=== $TAG projections start $(date '+%H:%M:%S')"
nfail=0
for f in "$W"/walk/*.bits(N); do
  b=$(basename "$f" .bits)
  /usr/bin/python3 "$M/project_f2.py" 4 4 5 "$f" --mode col --out "$W/proj_$b" --max "$PER" --quiet >> "$W/proj.log" 2>&1 || nfail=$(( nfail + 1 ))
  for g in "$W/proj_$b"/*.bits(N); do cp "$g" "$W/seeds/${b}_$(basename "$g")"; done
done
echo "    $(ls "$W/seeds" | wc -l | tr -d ' ') seeds, $nfail failed projection runs; ranks: $(ls "$W/seeds" | sed -E 's/.*proj444_([0-9]+)_.*/\1/' | sort -n | uniq -c | tr -s ' ' | tr '\n' ';')"
echo "=== $TAG descent start $(date '+%H:%M:%S') ($DMIN min, 12 threads)"
/opt/homebrew/bin/timeout $(( DMIN * 60 + 90 ))s "$F" 4 4 4 --seeds-dir "$W/seeds" --save-at 49 --write-at 47 --record 47 --minutes "$DMIN" --threads 12 --seed 1 --out "$W/d" --lift-below 0 --group-moves 0 > "$W/d.log" 2>&1
echo "    exit $? | $(grep -E '^c DONE' "$W/d.log" | tail -n 1) | 47 files: $(ls "$W/d" | wc -l | tr -d ' ')"
if [ "$(ls "$W/d" | wc -l | tr -d ' ')" -gt 0 ]; then
  echo "=== $TAG classes $(date '+%H:%M:%S')"
  /usr/bin/python3 "$L/matmul/tomar_line/proj/scheme_iso.py" 4 --classes "$S/reps" "$W/d" > "$W/iso.log" 2>&1
  grep -c 'new class representative' "$W/iso.log" | sed 's/^/    class representatives (5 known + new): /'
  grep 'new class representative' "$W/iso.log" | grep -v '/reps/' | sed 's/^/    NEW CLASS: /'
fi
echo "=== $TAG done $(date '+%H:%M:%S')"
