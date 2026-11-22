#!/bin/zsh
# products_build.zsh KRONEXACT STAGE CATALOG_ROOT [JOBS]
#   For every folder that products_repo.py stage wrote under STAGE/products, run kronexact INSIDE the folder on
#   the folder's own files, exactly as a reader would:
#     product    kronexact build  plan.json                     SCHEME.json --catalog CATALOG_ROOT
#     deletion   kronexact replay source_plan.json path_1.json  SCHEME.json --catalog CATALOG_ROOT
#   The output goes to the folder's certificate.log, the scheme is compressed with gzip -9 -n (no name, no time,
#   so the file is reproducible).  One line per folder is appended to work/progress beside STAGE.  Folders that already
#   have their scheme are skipped.  Removes nothing but the uncompressed scheme that gzip replaces.
# products_build.zsh --one KRONEXACT STAGE CATALOG_ROOT FOLDER KIND SCHEME   (one folder; used by the fan-out)
if [[ $1 == --one ]]; then
  KX=$2; ST=$3; CAT=$4; folder=$5; kind=$6; scheme=$7
  cd $ST/products/$folder || exit 1
  [[ -s $scheme.gz ]] && exit 0
  t0=$SECONDS
  if [[ $kind == product ]]; then
    timeout 3600 $KX build plan.json $scheme --catalog $CAT > certificate.log 2>&1
  else
    timeout 3600 $KX replay source_plan.json path_1.json $scheme --catalog $CAT > certificate.log 2>&1
  fi
  rc=$?
  [[ $rc == 0 && -s $scheme ]] && gzip -9 -n -f $scheme
  print "$folder exit $rc $((SECONDS - t0)) s: $(grep -E 'RESULT|panicked' certificate.log | head -1 | cut -c1-140)" >> $ST:h/work/progress
  exit 0
fi
KX=${1:A}; ST=${2:A}; CAT=${3:A}; J=${4:-12}
export RAYON_NUM_THREADS=2
cut -f1-3 $ST:h/work/jobs.tsv | tr '\t' ' ' | xargs -P $J -L 1 ${0:A} --one $KX $ST $CAT
print "ALL DONE $(date): $(grep -c ' exit 0 ' $ST:h/work/progress) of $(grep -c . $ST:h/work/jobs.tsv) built" >> $ST:h/work/progress
