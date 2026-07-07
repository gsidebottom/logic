#!/bin/zsh
# Run PLinOpt's optimizer over (a) their own 4x4x4:48 L/R/P as a
# control, (b) our 54 gauged slot-variant matrices.  For each matrix
# try the direct optimizer and the transposed-kernel pipeline
# (matrix-transpose | optimizer -K | transpozer), several randomized
# repeats each; count ops from the emitted SLP text (adds = +/- ops,
# shifts/mults = * ops; PLinOpt emits rational coefficient mults).
# Usage: run_plinopt.sh [REPEATS]
set -u
cd "$(dirname $0)"
P=plinopt/bin
export DYLD_LIBRARY_PATH=$PWD/stack/lib
REPS=${1:-8}
count_ops() {  # SLP on stdin -> "adds mults" (unary negation free)
  awk -F":=" '
    NF==2 {
      rhs=$2; gsub(/ /,"",rhs);
      n=gsub(/[+-]/,"",rhs); if (substr($2,1,1)=="-"||substr(rhs,1,1)=="") {}
      # leading sign of rhs is unary
      r2=$2; gsub(/ /,"",r2);
      if (substr(r2,1,1)=="-") n--;
      a+=n;
      m+=gsub(/\*/,"",r2);
    }
    END { print a+0, m+0 }'
}
best_for() {  # $1 = sms file -> prints "adds mults total"
  local f=$1 besta=99999 bestm=99999 bestt=99999
  for r in $(seq 1 $REPS); do
    for mode in direct kernel; do
      if [[ $mode == direct ]]; then
        out=$($P/optimizer "$f" 2>/dev/null | count_ops)
      else
        out=$($P/matrix-transpose "$f" 2>/dev/null \
              | $P/optimizer -K 2>/dev/null \
              | $P/transpozer 2>/dev/null | count_ops)
      fi
      a=${out%% *}; m=${out##* }
      t=$((a + m))
      if (( t > 0 && t < bestt )); then besta=$a; bestm=$m; bestt=$t; fi
    done
  done
  echo "$besta $bestm $bestt"
}

echo "=== control: their own matrices (expect ~104 / ~85 / ~152) ==="
for tag in L R P; do
  f=plinopt/data/4x4x4_48_rational_${tag}.sms
  [[ -f $f ]] || { echo "missing $f"; continue; }
  echo "their-$tag: $(best_for $f)"
done

echo "=== ours: 18 instances x 3 matrices ==="
typeset -A tot
for f in ours_sms/*_L.sms; do
  base=${f%_L.sms}
  name=${base##*/}
  l=$(best_for ${base}_L.sms); r=$(best_for ${base}_R.sms); p=$(best_for ${base}_P.sms)
  lt=${l##* }; rt=${r##* }; pt=${p##* }
  echo "$name: L=($l) R=($r) P=($p) TOTAL=$((lt + rt + pt))"
done
echo "PLINOPT-RUN-DONE"
