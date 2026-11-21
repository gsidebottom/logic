#!/bin/zsh
# delete_test.zsh N: one deletion (first and last index of every slot) + LITA's 2-reduction search on the N
# lowest-rank built product schemes, against Sedoglavic's table.  A screen modulo a prime.  Deletes nothing.
cd ${0:A:h}
K=${PWD:h:h:h:h:h}/target/release/kronkill
ST=$PWD/../2026-11-20_lita/status_table_8e6ad05.json
mkdir -p reduce/src reduce/dpaths
for f in $(ls built/*.json.gz | awk -F_m '{print $2+0, $0}' | sort -n | head -$1 | cut -d' ' -f2); do
  b=${${f:t}%.json.gz}
  [[ -e reduce/src/$b.json ]] || gzip -dc $f > reduce/src/$b.json
  n=(${(s:x:)${b%_m*}})
  # the scheme may be stored in another orientation: read its own dimensions
  d=($(python3 -c "import json,sys;print(*json.load(open(sys.argv[1]))['n'])" reduce/src/$b.json))
  seq="I0;J0;K0;I$((d[1]-1));J$((d[2]-1));K$((d[3]-1))"
  r=$(timeout 3600 $K reduce/src/$b.json "$seq" --threads 4 --status $ST --paths reduce/dpaths 2>&1 | grep -E 'alive|done' | sed 's/ *(.*//' | tr '\n' ';' | cut -c1-700)
  print "$b [$d]: $r" >> reduce/dprogress
done
print "DONE $(date)" >> reduce/dprogress
