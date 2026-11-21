#!/bin/zsh
# build_all.zsh KRONEXACT: builds every plan of plans/ with `kronexact build`, which certifies the result exactly
# (every Brent equation in integers, corrupted-copy control) before it writes it.  One log per plan, one line per
# plan in progress.  Skips plans whose scheme is already there.  Deletes nothing.
KX=$1
cd ${0:A:h}
mkdir -p built logs
for p in plans/*.plan.json; do
  b=${${p:t}%.plan.json}
  [[ -e built/$b.json.gz ]] && continue
  t0=$SECONDS
  timeout 3600 $KX build $p built/$b.json > logs/$b.log 2>&1
  rc=$?
  if [[ $rc == 0 && -s built/$b.json ]]; then gzip -9 -f built/$b.json; fi
  print "$b exit $rc $((SECONDS - t0)) s: $(grep -E 'RESULT|panicked' logs/$b.log | head -1 | cut -c1-160)" >> progress
done
print "ALL DONE $(date)" >> progress
