#!/bin/zsh
# LITA's squares 17^3 .. 32^3 (github.com/khoruzhii/lita at 472a79f, converted by lita_npz2json.py): single
# deletions of the first and last index of every slot (first only from 25^3 up), then the 2-reduction, by
# target/release/kronkill modulo 1048573.  Bar: Sedoglavic's table of 2026-11-15.  A screen: every line below
# the table still needs the exact replay over Q.
cd ${0:A:h}/../..
D=kron_runs/2026-11-20_lita; K=../../../target/release/kronkill; L=../../external/lita/json; ST=$D/status_table_8e6ad05.json
echo "singles start $(date)" >> $D/progress
for f in $L/*.json(on); do
  k=${${f:t}%%x*}
  (( k >= ${1:-17} )) || continue
  if (( k <= 24 )); then seqs="I0;J0;K0;I$((k-1));J$((k-1));K$((k-1))"; else seqs="I0;J0;K0"; fi
  s=$(date +%s)
  timeout 14400 $K $f "$seqs" --walk 100 --restarts 4 --status $ST --out $D/logs/singles_$k.csv --paths $D/paths/$k > $D/logs/singles_$k.log 2>&1
  rc=$?
  echo "singles $k exit $rc $(( $(date +%s) - s )) s: $(grep -o -- '-> [0-9]*; catalog Q [0-9]*' $D/logs/singles_$k.log | sort | uniq -c | tr '\n' ' ')" >> $D/progress
done
echo "singles ALL DONE $(date)" >> $D/progress
