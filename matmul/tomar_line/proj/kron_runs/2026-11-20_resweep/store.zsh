#!/bin/zsh
# store.zsh VERIFYDIR PATH.json : copy a verified re-sweep record into kron_reduced/ under the usual names
# (<sorted shape>_m<rank>_Q.{json.gz,path.json,reduce.log,semantic.log,deps files}); refuses to overwrite.
set -e
V=${1:A}; PJ=${2:A}; cd ${0:A:h}/../..
stem=${${PJ:t}%.path.json}; shape=${stem%%_m*}; m=${${stem#*_m}%%_*}; B=kron_reduced/${shape}_m${m}_Q
[ -e $B.json.gz ] && { echo "$B exists, not overwritten"; exit 0; }
grep -q 'VERIFIES EXACTLY; corrupted copy REJECTED' $V.log && grep -q '^end' $V.log && ! grep -qE 'FAILED|MISMATCH|DOES NOT' $V.log
fin=$(grep '^FINAL ' $V.log | cut -d' ' -f2); [ -f $fin ]
[ "$(python3 -I -c "import json,sys; print(json.load(open(sys.argv[1]))['m'])" $fin)" = "$m" ]
gzip -9 -c $fin > $B.json.gz; cp $PJ $B.path.json; cp $V.log $B.reduce.log
grep -A1 '^FINAL ' $V.log | tail -1 > $B.semantic.log
deps=($V/*.deps.json)
if (( $#deps == 1 )); then cp $deps[1] $B.deps.json; else for d in $deps; do t=${${d:t}%%_m*}; cp $d $B.$t.deps.json; done; fi
echo "stored $B: $(ls $B.* | wc -l | tr -d ' ') files"
