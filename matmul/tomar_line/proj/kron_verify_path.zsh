#!/bin/zsh
# kron_verify_path.zsh PATH.json OUTDIR
# Exact replay over Q of a kronkill path file (src/bin/kronkill.rs): for every stage the exact projection
# (kron_project.py, same product order as kronkill's), then every reduction step with kronkill's pivots
# (kron_reduce.py D --pivots: exact dependencies, both Brent routes, corrupted-copy control), then the
# independent checks on the final scheme (semantic, non-commutative, Kronecker ranks, coefficients, F_p).
set -u
PJ=${1:A}; OUT=${2:A}
cd ${0:A:h} || exit 1
mkdir -p $OUT
NST=$(python3 -c "import json,sys; d=json.load(open(sys.argv[1])); print(len(d['stages']))" $PJ)
SRC=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['source'])" $PJ)
CUR=$SRC
date "+start %H:%M:%S  $PJ"
for (( s=0; s<NST; s++ )); do
  DEL=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['stages'][$s]['delete'])" $PJ)
  if [[ -n "$DEL" ]]; then
    FLAG="--${DEL[1]}"; IDX=${DEL[2,-1]}
    python3 -I kron_project.py $CUR $OUT/s${s}_proj.json $FLAG $IDX || { echo "PROJECTION FAILED"; exit 1; }
    CUR=$OUT/s${s}_proj.json
  fi
  NSTEP=$(python3 -c "import json,sys; print(len(json.load(open(sys.argv[1]))['stages'][$s]['steps']))" $PJ)
  for (( t=0; t<NSTEP; t++ )); do
    read D PIV MOUT <<< "$(python3 -c "import json,sys; x=json.load(open(sys.argv[1]))['stages'][$s]['steps'][$t]; print(x['direction'], ','.join(map(str,x['pivots'])), x['m_out'])" $PJ)"
    NEXT=$OUT/s${s}_t${t}_m${MOUT}_Q.json
    timeout 3600 python3 kron_reduce.py $CUR $D $NEXT --pivots $PIV || { echo "REDUCTION FAILED at stage $s step $t"; exit 1; }
    M=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['m'])" $NEXT)
    [[ "$M" == "$MOUT" ]] || { echo "COUNT MISMATCH at stage $s step $t: exact $M, kronkill $MOUT"; exit 1; }
    CUR=$NEXT
  done
done
echo "FINAL $CUR"
python3 -I scheme_semantic_check.py $CUR 2 11
python3 -I scheme_noncomm_check.py $CUR
python3 kron_ranks_cli.py $CUR
python3 -I kron_coeff_stats.py $CUR
python3 -I scheme_modp_check.py $CUR 2,3,5,7,11,13,17,19 3
python3 -I scheme_modp_check.py $CUR 23,65537,1048573,998244353,2147483647,18446744069414584321 2
date "+end %H:%M:%S"
