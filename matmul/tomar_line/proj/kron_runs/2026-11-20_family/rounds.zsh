#!/bin/zsh
# Deep-walk rounds on the 15x15x15 family: every scheme in sources/rN, every single deletion in all three slots
# (kronkill next:, walk $WALK x $RESTARTS, default 2000 x 64); shapes below bar.txt are replayed exactly over Q
# (kron_verify_path.zsh), stored as sources/r(N+1) and lower the bar.  Stops when a round verifies nothing.
D0=${0:A:h}; cd $D0/../..
P=$PWD; D=$D0; W=${WALK:-2000}; R=${RESTARTS:-64}; K=${P:h:h:h}/target/release/kronkill; ST=$P/kron_runs/2026-11-19/status_f70078c.json
r=${1:-1}
while (( r <= 12 )); do
  srcs=($D/sources/r$r/*.json(N)); (( $#srcs )) || break
  echo "round $r: $#srcs sources, start $(date +%H:%M:%S)" >> $D/progress
  for f in $srcs; do
    tag=${f:t:r}
    timeout 7200 $K $f next: --walk $W --restarts $R --status $ST --bar "$(cat $D/bar.txt)" --out $D/logs/r${r}__$tag.csv --paths $D/paths/r$r/$tag > $D/logs/r${r}__$tag.log 2>&1
    rc=$?
    grep -E 'BELOW|BRENT' $D/logs/r${r}__$tag.log | sed "s|^|r$r $tag: |" >> $D/hits.txt
    [ $rc -ne 0 ] && echo "r$r $tag exit $rc: $(tail -1 $D/logs/r${r}__$tag.log | cut -c1-200)" >> $D/failures.txt
    echo "r$r $tag done $(date +%H:%M:%S): $(grep -c BELOW $D/logs/r${r}__$tag.log) below" >> $D/progress
  done
  # the lowest path of every shape, over all sources of the round
  todo=($(ls $D/paths/r$r/*/*.path.json 2>/dev/null | awk -F/ '{f=$NF; s=f; sub(/_m.*/,"",s); m=f; sub(/^[^_]*_m/,"",m); sub(/_.*/,"",m); if(!(s in b) || m+0<b[s]) {b[s]=m+0; p[s]=$0}} END{for(s in p) print p[s]}'))
  echo "round $r: $#todo shapes to verify, $(date +%H:%M:%S)" >> $D/progress
  n=0
  for pj in $todo; do
    tag=${pj:h:t}; stem=${${pj:t}%.path.json}; V=$D/verify/r$r/${tag}__$stem
    mkdir -p $V
    ( $P/kron_verify_path.zsh $pj $V > $V.log 2>&1 ) &
    (( ++n % 6 == 0 )) && wait
  done
  wait
  mkdir -p $D/sources/r$((r+1))
  for pj in $todo; do
    tag=${pj:h:t}; stem=${${pj:t}%.path.json}; V=$D/verify/r$r/${tag}__$stem; shape=${stem%%_m*}; m=${${stem#*_m}%%_*}
    fin=$(grep '^FINAL ' $V.log | cut -d' ' -f2)
    if grep -q 'VERIFIES EXACTLY; corrupted copy REJECTED' $V.log && grep -q '^end' $V.log && ! grep -qE 'FAILED|MISMATCH|DOES NOT' $V.log && [ -f "$fin" ]; then
      echo "VERIFIED r$r $shape $m from $tag ${stem##*_m${m}_}: $(grep -oE 'denominators: primes \[[^]]*\], max [0-9]+' $V.log | tail -1) $(grep -oE 'ranks \[[0-9, ]+\]' $V.log | tail -1)" >> $D/verified.txt
      cp $fin $D/sources/r$((r+1))/${shape}_m${m}_Q.json
      print -n ",$shape=$m" >> $D/bar.txt
    else
      echo "NOT VERIFIED r$r $shape $m from $tag $stem: $(grep -E 'FAILED|MISMATCH|DOES NOT|Error|SystemExit' $V.log | head -1 | cut -c1-150)" >> $D/verified.txt
    fi
  done
  echo "round $r done $(date +%H:%M:%S)" >> $D/progress
  r=$((r+1))
done
echo "ALL DONE $(date)" >> $D/progress; touch $D/finished
