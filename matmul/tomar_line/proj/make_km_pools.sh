#!/bin/zsh
# Projected 4x4 seed pools from Kauers-Moosbauer's <4,4,5>:60 over F2 (matmul/external/km_flips,
# 2026-11-07): one projection drops 4, so the seeds sit at 56 (AlphaTensor's 63 gave 59).  Four
# orientations: col on <4,4,5>, inner-a and inner-b on the rotation <4,5,4>, row on <5,4,4>
# (matmul/rotate_f2.py), 1500 seeds each, every projection checked against the 4x4 tensor.
# usage: make_km_pools.sh OUTROOT   (pools land in OUTROOT/seeds444_km_{col,ia,ib,row,all})
set -u
export PYTHONHASHSEED=0
OUT=${1:?outroot}
M=/Users/greg/projects/logic/matmul
B=$M/external/km_flips/km445_60.bits
mkdir -p "$OUT"
/usr/bin/python3 "$M/rotate_f2.py" 4 4 5 "$B" "$OUT/km454_60.bits"
/usr/bin/python3 "$M/rotate_f2.py" 4 4 5 "$B" "$OUT/km544_60.bits" --twice
proj() { # n1 n2 n3 in mode outname
  mkdir -p "$OUT/$6"
  /usr/bin/python3 "$M/project_f2.py" "$1" "$2" "$3" "$4" --mode "$5" --out "$OUT/$6" --max 1500 --quiet
  echo "$6: $(ls "$OUT/$6" | wc -l | tr -d ' ') seeds"
}
proj 4 4 5 "$B" col seeds444_km_col
proj 4 5 4 "$OUT/km454_60.bits" inner-a seeds444_km_ia
proj 4 5 4 "$OUT/km454_60.bits" inner-b seeds444_km_ib
proj 5 4 4 "$OUT/km544_60.bits" row seeds444_km_row
mkdir -p "$OUT/seeds444_km_all"
for d in seeds444_km_col seeds444_km_ia seeds444_km_ib seeds444_km_row; do for f in "$OUT/$d"/*.bits; do cp "$f" "$OUT/seeds444_km_all/${d}_$(basename "$f")"; done; done
echo "seeds444_km_all: $(ls "$OUT/seeds444_km_all" | wc -l | tr -d ' ') seeds"
