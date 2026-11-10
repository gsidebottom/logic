#!/bin/zsh
# Option 1b: parents of our own from the five rank-47 classes.  Each class representative embedded as a <4,4,5> of rank
# 63 (its 47 products plus the 16 trivial ones of the fifth column, proj/embed445.py); the five descended together in
# <4,4,5> for 20 minutes on 12 threads, landings below 63 written; the lowest 300 taken as parents, projected by col
# into 10 seeds each, a 20-minute <4,4,4> descent, the 47s class-sorted.  Waits for option 1's driver to finish.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/own445b
L=/Users/greg/projects/logic; M=$L/matmul; F=$L/target/release/flip; PROJ=$L/matmul/tomar_line/proj
REPS=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/wp/reps
export PYTHONHASHSEED=0
while ps -axo command | grep -q '[o]wn445/run.zsh'; do sleep 20; done
echo "=== 1b: <4,4,5> descent from the five embedded 63s, 20 min, 12 threads, start $(date '+%H:%M:%S')"
mkdir -p "$S/d445"
/opt/homebrew/bin/timeout 1350s "$F" 4 4 5 --seeds-dir "$S/parents63" --save-at 63 --write-at 62 --record 60 --minutes 20 --threads 12 --seed 1 --out "$S/d445" --lift-below 0 --group-moves 0 > "$S/d445.log" 2>&1
echo "    exit $? | $(grep -E '^c DONE' "$S/d445.log" | tail -n 1) | files $(ls "$S/d445" | wc -l | tr -d ' ')"
mkdir -p "$S/parents" "$S/seeds444"
/usr/bin/python3 - "$S" <<'PY'
import sys, os, re, shutil
from collections import Counter
S = sys.argv[1]; files = []
for f in os.listdir(os.path.join(S, 'd445')):
    m = re.match(r'r(\d+)-(\d+)\.bits$', f)
    if m: files.append((int(m.group(1)), f))
files.sort()
for rk, f in files[:300]:
    shutil.copy(os.path.join(S, 'd445', f), os.path.join(S, 'parents', f))
print('    written by rank:', sorted(Counter(r for r, _ in files).items()), '| parents taken:', len(files[:300]))
PY
for p in "$S"/parents/*.bits(N); do
  b=$(basename "$p" .bits)
  /usr/bin/python3 "$M/project_f2.py" 4 4 5 "$p" --mode col --out "$S/proj_$b" --max 10 --quiet >> "$S/proj.log" 2>&1
  for g in "$S/proj_$b"/*.bits(N); do cp "$g" "$S/seeds444/${b}_$(basename "$g")"; done
done
echo "    $(ls "$S/seeds444" | wc -l | tr -d ' ') 4x4 seeds; ranks: $(ls "$S/seeds444" | sed -E 's/.*proj444_([0-9]+)_.*/\1/' | sort -n | uniq -c | tr -s ' ' | tr '\n' ';')"
if [ "$(ls "$S/seeds444" | wc -l | tr -d ' ')" -eq 0 ]; then echo "no landings below 63: option 1b ends at the parent step $(date '+%H:%M:%S')"; exit 0; fi
echo "=== 1b: <4,4,4> descent from the own-parent pool, 20 min, 12 threads, start $(date '+%H:%M:%S')"
mkdir -p "$S/d444"
/opt/homebrew/bin/timeout 1350s "$F" 4 4 4 --seeds-dir "$S/seeds444" --save-at 49 --write-at 47 --record 47 --minutes 20 --threads 12 --seed 1 --out "$S/d444" --lift-below 0 --group-moves 0 > "$S/d444.log" 2>&1
echo "    exit $? | $(grep -E '^c DONE' "$S/d444.log" | tail -n 1) | 47 files $(ls "$S/d444" | wc -l | tr -d ' ')"
if [ "$(ls "$S/d444" | wc -l | tr -d ' ')" -gt 0 ]; then
  /usr/bin/python3 "$PROJ/scheme_iso.py" 4 --classes "$REPS" "$S/d444" > "$S/iso.log" 2>&1
  echo "    class representatives (5 known + new): $(grep -c 'new class representative' "$S/iso.log")"
  grep 'new class representative' "$S/iso.log" | grep -v '/reps/' | sed 's/^/    NEW CLASS: /'
  grep 'same class as' "$S/iso.log" | sed -E 's|.*same class as [^ ]*/reps/([a-z0-9_]+)\.bits.*|\1|' | sort | uniq -c | sed 's/^/    /'
fi
echo "=== option 1b done $(date '+%H:%M:%S')"
