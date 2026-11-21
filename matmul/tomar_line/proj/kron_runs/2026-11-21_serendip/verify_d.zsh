#!/bin/zsh
# verify_d.zsh KRONEXACT: exact replay over Q and exact Brent check (kronexact replay) of every path in
# reduce/dpaths; certified schemes go to reduce/exact.  Skips what is done.  Deletes nothing.
KX=$1
cd ${0:A:h}
mkdir -p reduce/exact reduce/xlogs
for p in reduce/dpaths/*.path.json; do
  b=${${p:t}%.path.json}
  [[ -e reduce/exact/$b.json.gz ]] && continue
  src=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['source'])" $p)
  timeout 7200 $KX replay $src $p reduce/exact/$b.json > reduce/xlogs/$b.log 2>&1
  rc=$?
  if [[ $rc == 0 && -s reduce/exact/$b.json ]]; then gzip -9 -f reduce/exact/$b.json; fi
  print "$b exit $rc: $(grep -E 'RESULT|panicked' reduce/xlogs/$b.log | head -1 | cut -c1-140)" >> reduce/verified.txt
done
