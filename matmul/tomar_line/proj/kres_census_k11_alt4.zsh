#!/bin/zsh
# Stored as run on 2026-11-12 from the session scratch directory (kres/deep/d4/d4.zsh): the scratch paths are kept;
# see matmul/session_data/README.md.  kres_d4 is src/bin/kres.rs as committed with this file (--shard, --progress).
# Jobs: proj/kres_census_k11_alt4_job.zsh.  Lines: the four representatives of the six projkm47_7 lines left open at
# depth 3 (line1..4.txt = 1,3,4,12,13,14,18,27,32,38,41 / 1,3,4,12,13,14,32,34,38,40,41 / 0,4,6,13,14,18,23,27,33,36,44 /
# 1,4,12,22,26,30,33,34,37,40,43; proj/kres_line_orbits.py maps the other two onto the last two).
# depth-4 pass over projkm47_7's open k = 11 alternative lines: every line split into N shards of the first-level
# loop (kres --shard), the jobs run by a pool of P single-threaded workers; driver log run/driver.log.
# (KLINES, not LINES: zsh's LINES is the terminal height, 0 here, and the first launch took it.)
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
D=$S/kres/deep/d4
KLINES=${KLINES:-"1 2 3 4"}; FIRST=${FIRST:-"4"}; N=${N:-96}; P=${P:-12}; CAP=${CAP:-7200}; SKIP=${SKIP:-""}
mkdir -p $D/run
echo "=== d4 start $(date '+%Y-%m-%d %H:%M:%S'): lines $KLINES ($FIRST first), $N shards each, $P workers, cap $CAP s per job, skipping [$SKIP]" >> $D/run/driver.log
# the heavy line first, then the others interleaved, so the tail is short; SKIP lists "line:shard" jobs already run
{ for l in ${=FIRST}; do for s in $(seq 0 $((N-1))); do echo "$l $s $N $CAP"; done; done
  for s in $(seq 0 $((N-1))); do for l in ${=KLINES}; do [[ " ${FIRST} " == *" $l "* ]] || echo "$l $s $N $CAP"; done; done; } \
  | while read l s n c; do [[ " ${SKIP} " == *" $l:$s "* ]] || echo "$l $s $n $c"; done > $D/run/jobs.txt
echo "    $(wc -l < $D/run/jobs.txt | tr -d ' ') jobs" >> $D/run/driver.log
xargs -P $P -L 1 $D/job.zsh < $D/run/jobs.txt
echo "=== d4 done $(date '+%Y-%m-%d %H:%M:%S')" >> $D/run/driver.log
