#!/bin/zsh
# 47-adjacency against flip distance: NM mutants at K flips from the parent (flipk_f2.py), each scored by pscore.zsh
# (60 projected seeds, a 6-second 12-thread descent); baseline = the parent itself under three descent seeds.
# usage: decay.zsh PARENT.bits NAME [NM=20] [KS="1 2 4 8 16 32 64 128"]
set -u
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/pspace
L=/Users/greg/projects/logic; PROJ=$L/matmul/tomar_line/proj
P=$1; NAME=$2; NM=${3:-20}; KS=${4:-"1 2 4 8 16 32 64 128"}
W=$S/$NAME; mkdir -p "$W/mut"
echo "=== decay $NAME start $(date '+%H:%M:%S') (parent $P, $NM mutants per distance, distances $KS)"
for s in 1 2 3; do /bin/zsh "$S/pscore.zsh" "$P" "base_s$s" "$W" 60 0.1 "$s"; done
for k in ${=KS}; do
  for m in $(seq 1 "$NM"); do
    mut=$W/mut/k${k}_m${m}.bits
    /usr/bin/python3 "$PROJ/flipk_f2.py" 4 4 5 "$P" "$k" "$mut" --seed $(( k * 1000 + m )) --quiet || { echo "k$k m$m: flipk failed"; continue; }
    /bin/zsh "$S/pscore.zsh" "$mut" "k${k}_m${m}" "$W" 60 0.1 1
  done
done
if [ "$(ls "$W/found47" | wc -l | tr -d ' ')" -gt 0 ]; then
  /usr/bin/python3 "$PROJ/scheme_iso.py" 4 --classes "$S/../wp/reps" "$W/found47" > "$W/iso.log" 2>&1
  echo "classes: $(grep -c 'new class representative' "$W/iso.log") representatives (5 known + new)"
  grep 'new class representative' "$W/iso.log" | grep -v '/reps/' | sed 's/^/    NEW CLASS: /'
fi
echo "=== decay $NAME done $(date '+%H:%M:%S')"
