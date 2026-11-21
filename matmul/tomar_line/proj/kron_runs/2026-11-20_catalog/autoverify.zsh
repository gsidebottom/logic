#!/bin/zsh
# Verify, exactly over Q, the best path of every shape under paths/ (one at a time), until the sweep has
# finished and nothing is left.  Results: verify/<path stem>.log; one summary line each in verified.txt.
cd ${0:A:h}/../..
C=kron_runs/2026-11-20_catalog
while true; do
  todo=""
  for shape in $(ls $C/paths | sed -E 's/_m[0-9]+_.*//' | sort -u); do
    best=$(ls $C/paths | grep "^${shape}_m" | sort -t_ -k2.2n | head -1); stem=${best%.path.json}
    [ -f $C/verify/$stem.log ] && continue
    todo=$stem; break
  done
  if [ -z "$todo" ]; then [ -f $C/finished ] && break; sleep 20; continue; fi
  nice -n 5 ./kron_verify_path.zsh $C/paths/$todo.path.json $C/verify/$todo > $C/verify/$todo.log 2>&1
  if grep -q 'VERIFIES EXACTLY; corrupted copy REJECTED' $C/verify/$todo.log && grep -q '^end' $C/verify/$todo.log && ! grep -qE 'FAILED|MISMATCH|DOES NOT' $C/verify/$todo.log; then
    echo "VERIFIED $todo $(grep -oE 'denominators: primes \[[^]]*\], max [0-9]+' $C/verify/$todo.log | tail -1) ranks $(grep -oE 'ranks \[[0-9, ]+\]' $C/verify/$todo.log | tail -1)" >> $C/verified.txt
  else
    echo "NOT VERIFIED $todo: $(grep -E 'FAILED|MISMATCH|DOES NOT|Error|SystemExit' $C/verify/$todo.log | head -1 | cut -c1-150)" >> $C/verified.txt
  fi
done
echo "AUTOVERIFY DONE" >> $C/verified.txt
