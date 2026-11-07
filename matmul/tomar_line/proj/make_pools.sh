#!/bin/zsh
# Projected seed pools (move 3): project AlphaTensor's F2 schemes of the next format
# down by the substitution method (matmul/project_f2.py) and collect the results.
# usage: make_pools.sh OUTROOT   (pools land in OUTROOT/seeds*)
set -u
export PYTHONHASHSEED=0  # the A/B pools were made without it: two capped pools differ in 84/1500 and 20/600 files
OUT=${1:?outroot}
L=/Users/greg/projects/logic
A=$L/matmul/external/alphatensor_f2
X=$L/matmul/x47/walkseeds
P=$L/matmul/project_f2.py
proj() { # n1 n2 n3 in mode outdir [max]
  mkdir -p "$OUT/$6"
  python3 "$P" $1 $2 $3 "$4" --mode $5 --out "$OUT/$6" --max ${7:-2000} --quiet
  echo "$6: $(ls "$OUT/$6" | wc -l | tr -d ' ') seeds"
}
# <3,3,4> from <3,3,5>:36 (col: 36 - 3 = 33) and <3,4,4>:38 (inner-a: 38 - 3 = 35; inner-b: 38 - 4 = 34)
proj 3 3 5 $A/at335_36.bits col     seeds334_from335
proj 3 4 4 $A/at344_38.bits inner-a seeds334_from344a
proj 3 4 4 $A/at344_38.bits inner-b seeds334_from344b 1500
# <4,4,4> from <4,4,5>:63 (col: 63 - 4 = 59)
proj 4 4 5 $A/at445_63.bits col     seeds444_from445 1500
# <3,4,4> from <3,4,5>:47 (col: 47 - 4 = 43) and the three published 4x4 47s (row: 47 - 4 = 43)
proj 3 4 5 $A/at345_47.bits col     seeds344_from345 1500
proj 4 4 4 $X/at47.bits     row     seeds344_from444_at47  600
proj 4 4 4 $X/km47.bits     row     seeds344_from444_km47  600
proj 4 4 4 $X/ref47.bits    row     seeds344_from444_ref47 600
# the pools the A/B ran from
mkdir -p "$OUT/seeds334_all" "$OUT/seeds344_all"
for d in seeds334_from335 seeds334_from344a seeds334_from344b; do for f in "$OUT/$d"/*.bits; do cp "$f" "$OUT/seeds334_all/${d}_$(basename $f)"; done; done
for d in seeds344_from345 seeds344_from444_at47 seeds344_from444_km47 seeds344_from444_ref47; do for f in "$OUT/$d"/*.bits; do cp "$f" "$OUT/seeds344_all/${d}_$(basename $f)"; done; done
echo "seeds334_all: $(ls "$OUT/seeds334_all" | wc -l | tr -d ' ')  seeds344_all: $(ls "$OUT/seeds344_all" | wc -l | tr -d ' ')"
