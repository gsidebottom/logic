#!/bin/zsh
# reduce_test.zsh N: LITA's 2-reduction search (kronkill, no deletion) on the N lowest-rank built product schemes.
# A screen modulo a prime; anything it finds needs kronexact replay.  Deletes nothing.
cd ${0:A:h}
K=${PWD:h:h:h:h:h}/target/release/kronkill
for f in $(ls built/*.json.gz | awk -F_m '{print $2+0, $0}' | sort -n | head -$1 | cut -d' ' -f2); do
  b=${${f:t}%.json.gz}
  [[ -e reduce/src/$b.json ]] || gzip -dc $f > reduce/src/$b.json
  r=$(timeout 1800 $K reduce/src/$b.json . --threads 4 --paths reduce/paths 2>&1 | tail -3 | tr '\n' ' ' | cut -c1-300)
  print "$b: $r" >> reduce/progress
done
print "DONE $(date)" >> reduce/progress
