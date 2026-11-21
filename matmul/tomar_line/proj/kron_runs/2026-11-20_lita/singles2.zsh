#!/bin/zsh
# singles2.zsh WAITPID FIRST_K: continuation of singles.zsh with bounded memory.  Waits for the kronkill of the
# previous square (WAITPID), then the squares FIRST_K .. 32: deletions I0, J0, K0, one kronkill at a time from
# 29^3 up (three in parallel hold about 3 GB per (rank / 7500)^2 each).
cd ${0:A:h}/../..
D=kron_runs/2026-11-20_lita; K=../../../target/release/kronkill; L=../../external/lita/json; ST=$D/status_table_8e6ad05.json
while kill -0 $1 2>/dev/null; do sleep 10; done
k0=$(( $2 - 1 ))
echo "singles $k0 (handed over): $(grep -o -- '-> [0-9]*; catalog Q [0-9]*' $D/logs/singles_$k0.log | sort | uniq -c | tr '\n' ' ')" >> $D/progress
for f in $L/*.json(on); do
  k=${${f:t}%%x*}
  (( k >= $2 )) || continue
  s=$(date +%s)
  if (( k <= 28 )); then
    timeout 14400 $K $f "I0;J0;K0" --walk 100 --restarts 4 --status $ST --out $D/logs/singles_$k.csv --paths $D/paths/$k > $D/logs/singles_$k.log 2>&1
  else
    : > $D/logs/singles_$k.log
    for q in I0 J0 K0; do
      timeout 14400 $K $f $q --walk 100 --restarts 4 --status $ST --out $D/logs/singles_${k}_$q.csv --paths $D/paths/$k >> $D/logs/singles_$k.log 2>&1
    done
  fi
  echo "singles $k exit $? $(( $(date +%s) - s )) s: $(grep -o -- '-> [0-9]*; catalog Q [0-9]*' $D/logs/singles_$k.log | sort | uniq -c | tr '\n' ' ')" >> $D/progress
done
echo "singles ALL DONE $(date)" >> $D/progress
