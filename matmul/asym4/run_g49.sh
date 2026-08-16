#!/bin/zsh
set -u; cd "$(dirname $0)"; P=../dps48/plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/../dps48/stack/lib
REPS=${1:-24}
# ops from an SLP; prints "-1" only if the optimizer emitted nothing
count_ops() { awk -F":=" 'NF==2 { seen=1; r2=$2; gsub(/ /,"",r2);
    n=gsub(/[+-]/,"",r2); if (substr(r2,1,1)=="-") n--; a+=n; m+=gsub(/\*/,"",r2) }
  END { if (seen) print a+0+m+0; else print -1 }'; }
best_for() { local f=$1 bestt=99999
  for r in $(seq 1 $REPS); do for mode in direct kernel; do
      if [[ $mode == direct ]]; then t=$($P/optimizer "$f" 2>/dev/null | count_ops)
      else t=$($P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null \
               | $P/transpozer 2>/dev/null | count_ops); fi
      (( t >= 0 && t < bestt )) && bestt=$t
  done; done; echo "$bestt"; }
for fam in g49; do
  best=99999; bestk=-1
  for k in 0 1 2 3 4 5; do
    l=$(best_for ${fam}_o${k}_L.sms); r=$(best_for ${fam}_o${k}_R.sms); p=$(best_for ${fam}_o${k}_P.sms)
    on=$((r+p)); echo "$fam o$k: L=$l R=$r P=$p | total=$((l+r+p)) online(free L)=$on"
    (( on < best )) && { best=$on; bestk=$k; }
  done
  echo "${fam}-BEST-ONLINE=$best (orientation $bestk)"
done
