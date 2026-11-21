#!/bin/zsh
# build_dir.zsh KRONEXACT PLAN_DIR: as build_all.zsh, for the plans of PLAN_DIR.  Deletes nothing.
KX=$1; PD=$2
cd ${0:A:h}
mkdir -p built logs
for p in $PD/*.plan.json; do
  b=${${p:t}%.plan.json}
  [[ -e built/$b.json.gz ]] && continue
  t0=$SECONDS
  timeout 3600 $KX build $p built/$b.json > logs/$b.log 2>&1
  rc=$?
  if [[ $rc == 0 && -s built/$b.json ]]; then gzip -9 -f built/$b.json; fi
  print "$b exit $rc $((SECONDS - t0)) s: $(grep -E 'RESULT|panicked' logs/$b.log | head -1 | cut -c1-160)" >> progress_${PD:t}
done
print "ALL DONE $(date)" >> progress_${PD:t}
