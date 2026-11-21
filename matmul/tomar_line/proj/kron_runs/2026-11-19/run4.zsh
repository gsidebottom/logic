#!/bin/zsh
cd ${0:A:h}/../..
D=kron_runs/2026-11-19; L=../../perminov_cache/repo/schemes/known/lita; B='13x14x14=1563,15x16x16=2202'
Is() { python3 -c "print(';'.join(f'I{i}' for i in range($1)))" }
run() { local tag=$1 src=$2 seqs=$3; echo "start $tag $(date +%H:%M:%S)" >> $D/run4.progress
  python3 kron_proj_multi.py $src $D/status_f70078c.json $D/deep4_$tag.csv "$seqs" --workers 12 --walk 400 --restarts 4 --paths $D/paths --bar $B > $D/deep4_$tag.log 2>&1
  echo "end $tag $(date +%H:%M:%S) exit $?" >> $D/run4.progress; }
run 1379 $L/13x13x13_m1379_Q.json "$(Is 13)"
run 1594 $L/14x14x14_m1594_Q.json "$(Is 14)"
run 2237 $L/16x16x16_m2237_Q.json "$(Is 16)"
run 1977 $L/15x15x15_m1977_Q.json "$(Is 15)"
run 1977_nextI0 $L/15x15x15_m1977_Q.json "next:I0"
echo "ALL DONE $(date)" > $D/run4.done
