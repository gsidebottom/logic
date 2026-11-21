#!/bin/zsh
# chain.zsh LIST TAG: for every line "name /abs/source.json SEQ ..." of LIST, one more deletion in every slot
# after SEQ (kronkill next:SEQ, walk 400 x 4, each stage reduced), against the current bar.
cd ${0:A:h}/../..
P=$PWD; D=$P/kron_runs/2026-11-20_resweep; K=${P:h:h:h}/target/release/kronkill; ST=$P/kron_runs/2026-11-19/status_f70078c.json
L=$1; T=$2
mkdir -p $D/logs_$T
while read name src seq rest; do
  o=${name}__${seq//,/_}
  [ -f $D/logs_$T/$o.done ] && continue
  timeout 3600 $K $src next:$seq --walk 400 --restarts 4 --status $ST --bar "$(cat $D/bar.txt)" --out $D/logs_$T/$o.csv --paths $D/paths/$T/$name > $D/logs_$T/$o.log 2>&1
  rc=$?
  grep -E 'BELOW|BRENT' $D/logs_$T/$o.log | sed "s|^|$T $o: |" >> $D/hits.txt
  [ $rc -ne 0 ] && echo "$T $o exit $rc: $(tail -1 $D/logs_$T/$o.log | cut -c1-200)" >> $D/failures.txt
  echo "$T $o done $(date +%H:%M:%S): $(grep -c BELOW $D/logs_$T/$o.log) below" >> $D/progress
  touch $D/logs_$T/$o.done
done < $D/$L
echo "CHAIN $T DONE $(date)" >> $D/progress; touch $D/finished_$T
