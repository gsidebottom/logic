#!/bin/zsh
# score a <4,4,5> parent: project (col, MAXS seeds) and descend MIN minutes on 12 threads; print the DONE line; collect 47s
# usage: pscore.zsh PARENT.bits TAG WORKDIR [MAXS=60] [MIN=0.1] [DSEED=1]
set -u
L=/Users/greg/projects/logic; M=$L/matmul; F=$L/target/release/flip
P=$1; TAG=$2; W=$3; MAXS=${4:-60}; MIN=${5:-0.1}; DSEED=${6:-1}
export PYTHONHASHSEED=0
rm -rf "$W/$TAG"; mkdir -p "$W/$TAG/seeds" "$W/$TAG/d" "$W/found47"
/usr/bin/python3 "$M/project_f2.py" 4 4 5 "$P" --mode col --out "$W/$TAG/seeds" --max "$MAXS" --quiet > "$W/$TAG/proj.log" 2>&1
ns=$(ls "$W/$TAG/seeds" | wc -l | tr -d ' ')
/opt/homebrew/bin/timeout 120s "$F" 4 4 4 --seeds-dir "$W/$TAG/seeds" --save-at 49 --write-at 47 --record 47 --minutes "$MIN" --threads 12 --seed "$DSEED" --out "$W/$TAG/d" --lift-below 0 --group-moves 0 > "$W/$TAG/d.log" 2>&1
done_line=$(grep -E '^c DONE' "$W/$TAG/d.log" | tail -n 1)
n47=$(ls "$W/$TAG/d" | wc -l | tr -d ' ')
for f in "$W/$TAG/d"/*.bits(N); do cp "$f" "$W/found47/${TAG}_$(basename "$f")"; done
rm -rf "$W/$TAG/seeds"
echo "$TAG seeds $ns | $done_line | 47 files $n47"
