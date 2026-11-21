#!/bin/zsh
# build.zsh LIST : for every line "NAME|JSON.gz|COMMENT" write mat_mul/schemes/NAME/ in PLinOpt format:
# NAME_{L,R,P}.sms (json2sms.py, which re-reads and checks them), a program per map that stays in the scheme's
# coefficient ring (ring_slp.py, exact symbolic check; then PLinOpt's SLPchecker against the matrix), and the
# catalog-layout JSON.  Log: build2.log next to this script.
cd ${0:A:h}/../..
W=${0:A:h}; M=/Users/greg/projects/mat_mul; PL=/Users/greg/projects/logic/matmul/dps48/plinopt_pr/records
one() {
  local name=$1 js=$2 cm=$3 d=$M/schemes/$1
  mkdir -p $d
  python3 json2sms.py $js $d/$name --comment "$cm" > $W/$name.sms.log 2>&1 || { echo "$name SMS FAILED" >> $W/build2.log; return; }
  python3 ring_slp.py $d/$name > $W/$name.slp.log 2>&1 || { echo "$name SLP FAILED: $(tail -1 $W/$name.slp.log)" >> $W/build2.log; return; }
  local chk=""
  for s in L R P; do chk+="$($PL/bin/SLPchecker -M $d/${name}_$s.sms $d/${name}_$s.slp 2>&1 | grep -oE 'SUCCESS|ERROR|FAIL' | head -1) "; done
  cp $js $d/${js:t}
  echo "$name built $(date +%H:%M:%S): $(grep -o 'ALL EXACT.*REJECTED' $W/$name.sms.log); $(tail -1 $W/$name.slp.log | sed 's/.*total //'); SLPchecker $chk" >> $W/build2.log
}
n=0
while IFS='|' read name js cm; do
  one $name $js "$cm" &
  (( ++n % 6 == 0 )) && wait
done < $1
wait
echo "BUILD ${1:t} DONE $(date +%H:%M:%S)" >> $W/build2.log
