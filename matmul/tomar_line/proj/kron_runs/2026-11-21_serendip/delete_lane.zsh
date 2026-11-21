#!/bin/zsh
# delete_lane.zsh LO HI [THREADS]: one deletion (first and last index of every slot) + LITA's 2-reduction search
# (kronkill, modulo a prime: a screen) on every built product scheme with LO < rank <= HI, lowest rank first,
# against Sedoglavic's table.  Skips schemes already in reduce/dprogress.  Deletes nothing.
cd ${0:A:h}
K=${PWD:h:h:h:h:h}/target/release/kronkill
ST=$PWD/../2026-11-20_lita/status_table_8e6ad05.json
mkdir -p reduce/src reduce/dpaths
for f in $(ls built/*.json.gz | awk -F_m '{print $2+0, $0}' | sort -n | awk -v lo=$1 -v hi=$2 '$1>lo && $1<=hi {print $2}'); do
  b=${${f:t}%.json.gz}
  grep -q "^$b " reduce/dprogress 2>/dev/null && continue
  [[ -e reduce/src/$b.json ]] || gzip -dc $f > reduce/src/$b.json
  d=($(python3 -c "import json,sys;print(*json.load(open(sys.argv[1]))['n'])" reduce/src/$b.json))
  seq="I0;J0;K0;I$((d[1]-1));J$((d[2]-1));K$((d[3]-1))"
  r=$(timeout 7200 $K reduce/src/$b.json "$seq" --threads ${3:-4} --status $ST --paths reduce/dpaths 2>&1 | grep -E 'alive|done' | sed 's/ *(.*//' | tr '\n' ';' | cut -c1-900)
  print "$b [$d]: $r" >> reduce/dprogress
done
print "DONE $1 $2 $(date)" >> reduce/dprogress
