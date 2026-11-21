#!/bin/zsh
# Alternates pass: for every near-record single deletion in alt_list.txt (round, source, sequence), one more
# deletion in every slot (kronkill next:SEQ, walk 400 x 4), against the current bar.
cd ${0:A:h}/../..
P=$PWD; D=$P/kron_runs/2026-11-20_resweep; K=${P:h:h:h}/target/release/kronkill; ST=$P/kron_runs/2026-11-19/status_f70078c.json
L=${1:-alt_list.txt}; T=${2:-alt}
mkdir -p $D/logs_$T
while read r tag seq rest; do
  o=${r}__${tag}__$seq
  timeout 3600 $K $D/sources/$r/$tag.json next:$seq --walk 400 --restarts 4 --status $ST --bar "$(cat $D/bar.txt)" --out $D/logs_$T/$o.csv --paths $D/paths/$T/${r}__$tag > $D/logs_$T/$o.log 2>&1
  rc=$?
  grep -E 'BELOW|BRENT' $D/logs_$T/$o.log | sed "s|^|$T $o: |" >> $D/hits.txt
  [ $rc -ne 0 ] && echo "$T $o exit $rc: $(tail -1 $D/logs_$T/$o.log | cut -c1-200)" >> $D/failures.txt
  echo "$T $o done $(date +%H:%M:%S): $(grep -c BELOW $D/logs_$T/$o.log) below" >> $D/progress
done < $D/$L
echo "ALT $T DONE $(date)" >> $D/progress; touch $D/finished_$T
