#!/bin/zsh
# Option 1 (Greg, 2026-11-09 20:08): parents of our own.  Descend <4,4,5> with the flip engine from 200 projected seeds
# (the catalog's <4,4,6> and <4,5,5> schemes one projection up, ranks 69-72) and from the trivial scheme; take the
# lowest written <4,4,5> schemes (at most 300) as parents, project each by col into 10 seeds, descend <4,4,4> for 20
# minutes on 12 threads, class-sort every 47 against the five known representatives.
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/own445
L=/Users/greg/projects/logic; M=$L/matmul; F=$L/target/release/flip; PROJ=$L/matmul/tomar_line/proj
REPS=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/wp/reps
export PYTHONHASHSEED=0
while ps -axo command | grep -q '[d]ecay.zsh'; do sleep 20; done
echo "=== arm 1: <4,4,5> descent from 200 projected seeds (69-72), 20 min, 12 threads, start $(date '+%H:%M:%S')"
mkdir -p "$S/d445"
/opt/homebrew/bin/timeout 1350s "$F" 4 4 5 --seeds-dir "$S/seeds445" --save-at 66 --write-at 64 --record 60 --minutes 20 --threads 12 --seed 1 --out "$S/d445" --lift-below 0 --group-moves 0 > "$S/d445.log" 2>&1
echo "    exit $? | $(grep -E '^c DONE' "$S/d445.log" | tail -n 1) | files $(ls "$S/d445" | wc -l | tr -d ' ')"
echo "=== arm 2: <4,4,5> descent from the trivial scheme (80), 10 min, 12 threads, start $(date '+%H:%M:%S')"
mkdir -p "$S/d445triv"
/opt/homebrew/bin/timeout 750s "$F" 4 4 5 --trivial --save-at 68 --write-at 66 --record 60 --minutes 10 --threads 12 --seed 1 --out "$S/d445triv" --lift-below 0 --group-moves 0 > "$S/d445triv.log" 2>&1
echo "    exit $? | $(grep -E '^c DONE' "$S/d445triv.log" | tail -n 1) | files $(ls "$S/d445triv" | wc -l | tr -d ' ')"
echo "=== parents: lowest written <4,4,5> schemes, at most 300, $(date '+%H:%M:%S')"
mkdir -p "$S/parents"
/usr/bin/python3 - "$S" <<'PY'
import sys, os, re, shutil
S = sys.argv[1]; files = []
for d in ('d445', 'd445triv'):
    for f in os.listdir(os.path.join(S, d)):
        m = re.match(r'r(\d+)-(\d+)\.bits$', f)
        if m: files.append((int(m.group(1)), d, f))
files.sort()
for rk, d, f in files[:300]:
    shutil.copy(os.path.join(S, d, f), os.path.join(S, 'parents', f'{d}_{f}'))
from collections import Counter
print('    written by rank:', sorted(Counter(r for r, _, _ in files).items()), '| parents taken:', len(files[:300]), 'ranks', sorted(Counter(r for r, _, _ in files[:300]).items()))
PY
mkdir -p "$S/seeds444"
for p in "$S"/parents/*.bits(N); do
  b=$(basename "$p" .bits)
  /usr/bin/python3 "$M/project_f2.py" 4 4 5 "$p" --mode col --out "$S/proj_$b" --max 10 --quiet >> "$S/proj.log" 2>&1
  for g in "$S/proj_$b"/*.bits(N); do cp "$g" "$S/seeds444/${b}_$(basename "$g")"; done
done
echo "    $(ls "$S/seeds444" | wc -l | tr -d ' ') 4x4 seeds; ranks: $(ls "$S/seeds444" | sed -E 's/.*proj444_([0-9]+)_.*/\1/' | sort -n | uniq -c | tr -s ' ' | tr '\n' ';')"
if [ "$(ls "$S/seeds444" | wc -l | tr -d ' ')" -eq 0 ]; then echo "no seeds: option 1 ends at the parent step"; exit 0; fi
echo "=== <4,4,4> descent from the own-parent pool, 20 min, 12 threads, start $(date '+%H:%M:%S')"
mkdir -p "$S/d444"
/opt/homebrew/bin/timeout 1350s "$F" 4 4 4 --seeds-dir "$S/seeds444" --save-at 49 --write-at 47 --record 47 --minutes 20 --threads 12 --seed 1 --out "$S/d444" --lift-below 0 --group-moves 0 > "$S/d444.log" 2>&1
echo "    exit $? | $(grep -E '^c DONE' "$S/d444.log" | tail -n 1) | 47 files $(ls "$S/d444" | wc -l | tr -d ' ')"
if [ "$(ls "$S/d444" | wc -l | tr -d ' ')" -gt 0 ]; then
  /usr/bin/python3 "$PROJ/scheme_iso.py" 4 --classes "$REPS" "$S/d444" > "$S/iso.log" 2>&1
  echo "    class representatives (5 known + new): $(grep -c 'new class representative' "$S/iso.log")"
  grep 'new class representative' "$S/iso.log" | grep -v '/reps/' | sed 's/^/    NEW CLASS: /'
  grep 'same class as' "$S/iso.log" | sed -E 's|.*same class as [^ ]*/reps/([a-z0-9_]+)\.bits.*|\1|' | sort | uniq -c | sed 's/^/    /'
fi
echo "=== option 1 done $(date '+%H:%M:%S')"
