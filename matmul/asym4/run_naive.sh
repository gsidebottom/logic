#!/bin/zsh
set -u; cd "$(dirname $0)"; P=../dps48/plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/../dps48/stack/lib
REPS=${1:-24}
count_ops() { awk -F":=" 'NF==2 { r2=$2; gsub(/ /,"",r2); n=gsub(/[+-]/,"",r2);
  if (substr(r2,1,1)=="-") n--; a+=n; m+=gsub(/\*/,"",r2); } END { print a+0, m+0 }'; }
best_for() { local f=$1 bestt=99999
  for r in $(seq 1 $REPS); do for mode in direct kernel; do
      if [[ $mode == direct ]]; then out=$($P/optimizer "$f" 2>/dev/null | count_ops)
      else out=$($P/matrix-transpose "$f" 2>/dev/null | $P/optimizer -K 2>/dev/null | $P/transpozer 2>/dev/null | count_ops); fi
      a=${out%% *}; m=${out##* }; t=$((a+m)); (( t > 0 && t < bestt )) && bestt=$t
  done; done; echo "$bestt"; }
best=99999
for k in 0 1 2 3 4 5; do
  l=$(best_for n64_o${k}_L.sms); r=$(best_for n64_o${k}_R.sms); p=$(best_for n64_o${k}_P.sms)
  on=$((r+p)); echo "n64 o$k: L=$l R=$r P=$p | total=$((l+r+p)) online(free L)=$on"
  (( on < best )) && best=$on
done
echo "NAIVE64-BEST-ONLINE=$best"
