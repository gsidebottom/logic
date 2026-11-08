#!/bin/zsh
# Projected 4x4 seed pools from AlphaEvolve's <4,4,5>:61 reduced mod 2 (matmul/external/ae445, 2026-11-08):
# one projection drops 4, so the seeds sit at 57.  Four orientations as for the Kauers-Moosbauer parent
# (make_km_pools.sh): col on <4,4,5>, inner-a and inner-b on the rotation <4,5,4>, row on <5,4,4>, 1500 seeds
# each, every projection checked against the 4x4 tensor.
# usage: make_ae_pools.sh OUTROOT   (pools land in OUTROOT/seeds444_ae_{col,ia,ib,row,all})
set -u
export PYTHONHASHSEED=0
OUT=${1:?outroot}
M=/Users/greg/projects/logic/matmul
B=$M/external/ae445/ae445_61.bits
mkdir -p "$OUT"
/usr/bin/python3 "$M/rotate_f2.py" 4 4 5 "$B" "$OUT/ae454_61.bits"
/usr/bin/python3 "$M/rotate_f2.py" 4 4 5 "$B" "$OUT/ae544_61.bits" --twice
proj() { # n1 n2 n3 in mode outname
  mkdir -p "$OUT/$6"
  /usr/bin/python3 "$M/project_f2.py" "$1" "$2" "$3" "$4" --mode "$5" --out "$OUT/$6" --max 1500 --quiet
  echo "$6: $(ls "$OUT/$6" | wc -l | tr -d ' ') seeds"
}
proj 4 4 5 "$B" col seeds444_ae_col
proj 4 5 4 "$OUT/ae454_61.bits" inner-a seeds444_ae_ia
proj 4 5 4 "$OUT/ae454_61.bits" inner-b seeds444_ae_ib
proj 5 4 4 "$OUT/ae544_61.bits" row seeds444_ae_row
mkdir -p "$OUT/seeds444_ae_all"
for d in seeds444_ae_col seeds444_ae_ia seeds444_ae_ib seeds444_ae_row; do for f in "$OUT/$d"/*.bits; do cp "$f" "$OUT/seeds444_ae_all/${d}_$(basename "$f")"; done; done
echo "seeds444_ae_all: $(ls "$OUT/seeds444_ae_all" | wc -l | tr -d ' ') seeds"
