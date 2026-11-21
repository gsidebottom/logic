#!/bin/zsh
# Whole-catalog sweep: for every JSON scheme of Perminov's catalog (origin f70078c), the direct 2-reduction
# ('.') and every single-index deletion (next:), walk 400 x 4, by target/release/kronkill.
cd ${0:A:h}/../..
D=kron_runs/2026-11-20_catalog; K=../../../target/release/kronkill; ST=kron_runs/2026-11-19/status_f70078c.json
B='13x14x14=1563,15x16x16=2202'
# (the LITA deep walks finished before this restart)
echo "start $(date)" >> $D/progress
i=0
for f in $(cat $D/files.txt); do
  i=$((i+1)); f=../../../$f; tag=$(basename ${f:h})__$(basename $f .json)
  grep -qxF "$tag" $D/done.txt 2>/dev/null && continue
  for spec in . next:; do
    s=$([ $spec = . ] && echo direct || echo singles)
    timeout 3600 $K $f $spec --walk 400 --restarts 4 --status $ST --bar $B --out $D/logs/${tag}__$s.csv --paths $D/paths > $D/logs/${tag}__$s.log 2>&1
    rc=$?
    grep -E 'BELOW|BRENT' $D/logs/${tag}__$s.log | sed "s|^|$tag $s: |" >> $D/hits.txt
    [ $rc -ne 0 ] && echo "$tag $s exit $rc: $(tail -1 $D/logs/${tag}__$s.log | cut -c1-200)" >> $D/failures.txt
  done
  echo "$tag" >> $D/done.txt
  (( i % 50 == 0 )) && echo "$i files $(date +%H:%M:%S)" >> $D/progress
done
echo "ALL DONE $(date)" >> $D/progress; touch $D/finished
