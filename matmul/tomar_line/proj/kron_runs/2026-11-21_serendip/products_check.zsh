#!/bin/zsh
# products_check.zsh KRONEXACT CHECK_JSON STAGE [JOBS]
#   The two checks of mat_mul's `EXACT=1 tools/check_large.sh products`, run file by file in parallel on the
#   staged schemes: CHECK_JSON (tools/check_json.py: random matrices modulo four primes) and KRONEXACT check
#   (every Brent equation in exact integers).  The per-file outputs go to work/check/ beside STAGE and are joined in
#   the script's order into STAGE/checks/check_products.log, which is what the script itself would print.
#   Deletes nothing.
# products_check.zsh --one KRONEXACT CHECK_JSON STAGE FILE    (one scheme; used by the fan-out)
if [[ $1 == --one ]]; then
  KX=$2; CJ=$3; ST=$4; f=$5
  o=$ST:h/work/check/${${f:h}:t}.txt
  [[ -s $o ]] && exit 0
  { python3 -I $CJ $f 2; print "rc1 $?" > $o.rc
    $KX check $f | grep -E 'Brent equations|changed|RESULT' | sed 's/^/  /'; print "rc2 ${pipestatus[1]}" >> $o.rc } > $o.tmp 2>&1
  mv $o.tmp $o
  exit 0
fi
SELF=${0:A}; KX=${1:A}; CJ=${2:A}; ST=${3:A}; J=${4:-12}
export RAYON_NUM_THREADS=2
mkdir -p $ST:h/work/check $ST/checks
cd $ST
print -l products/*/*x*x*_m*.json.gz | xargs -P $J -L 1 $SELF --one $KX $CJ $ST
fail=0
{ for f in products/*/*x*x*_m*.json.gz; do
    o=$ST:h/work/check/${${f:h}:t}.txt
    cat $o
    grep -q '^rc1 0$' $o.rc && grep -q '^rc2 0$' $o.rc || fail=1
  done
  (( fail == 0 )) && print "ALL PRODUCTS SCHEMES PASS" || print "SOME PRODUCTS SCHEME FAILED"
} > checks/check_products.log
tail -1 checks/check_products.log
