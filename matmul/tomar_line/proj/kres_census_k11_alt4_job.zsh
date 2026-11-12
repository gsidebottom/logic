#!/bin/zsh
# Stored as run on 2026-11-12 from the session scratch directory (kres/deep/d4/job.zsh); one job of
# proj/kres_census_k11_alt4.zsh.
# one job of the depth-4 pass: line L (file lineL.txt), shard I of N; single-threaded; capped
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
D=$S/kres/deep/d4; K=$S/kres/build/kres_d4
L=$1; I=$2; N=$3; CAP=$4
O=$D/run/l${L}_s${I}
t0=$(date +%s)
nice -n 10 /opt/homebrew/bin/timeout ${CAP}s "$K" 4 4 4 "$S/wp/reps/projkm47_7.bits" --lines "$D/line$L.txt" --mode alt --maxdelta-alt 4 --threads 1 --shard $I/$N --progress --out "$O.txt" > "$O.log" 2>&1
ex=$?
v=$(grep -E '^c k=11:' "$O.log" | head -1)
echo "l$L s$I/$N exit $ex ${v:-no verdict} $(( $(date +%s) - t0 )) s $(date '+%H:%M:%S')" >> "$D/run/driver.log"
