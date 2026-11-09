#!/bin/zsh
# Projected 4x4 seed pools from Moosbauer's <4,4,5>:62 over Z reduced mod 2 (matmul/external/mb445, 2026-11-09):
# the seeds sit wherever one projection lands (62 minus the products supported only on the dropped slice).  Four orientations as for the Kauers-Moosbauer parent
# (make_km_pools.sh): col on <4,4,5>, inner-a and inner-b on the rotation <4,5,4>, row on <5,4,4>, 1500 seeds
# each, every projection checked against the 4x4 tensor.
# usage: make_mb_pools.sh OUTROOT   (pools land in OUTROOT/seeds444_mb_{col,ia,ib,row,all})
set -u
export PYTHONHASHSEED=0
OUT=${1:?outroot}
M=/Users/greg/projects/logic/matmul
B=$M/external/mb445/mb445_62_mod2.bits
mkdir -p "$OUT"
/usr/bin/python3 "$M/rotate_f2.py" 4 4 5 "$B" "$OUT/mb454_62.bits"
/usr/bin/python3 "$M/rotate_f2.py" 4 4 5 "$B" "$OUT/mb544_62.bits" --twice
proj() { # n1 n2 n3 in mode outname
  mkdir -p "$OUT/$6"
  /usr/bin/python3 "$M/project_f2.py" "$1" "$2" "$3" "$4" --mode "$5" --out "$OUT/$6" --max 1500 --quiet
  echo "$6: $(ls "$OUT/$6" | wc -l | tr -d ' ') seeds"
}
proj 4 4 5 "$B" col seeds444_mb_col
proj 4 5 4 "$OUT/mb454_62.bits" inner-a seeds444_mb_ia
proj 4 5 4 "$OUT/mb454_62.bits" inner-b seeds444_mb_ib
proj 5 4 4 "$OUT/mb544_62.bits" row seeds444_mb_row
mkdir -p "$OUT/seeds444_mb_all"
for d in seeds444_mb_col seeds444_mb_ia seeds444_mb_ib seeds444_mb_row; do for f in "$OUT/$d"/*.bits; do cp "$f" "$OUT/seeds444_mb_all/${d}_$(basename "$f")"; done; done
echo "seeds444_mb_all: $(ls "$OUT/seeds444_mb_all" | wc -l | tr -d ' ') seeds"
