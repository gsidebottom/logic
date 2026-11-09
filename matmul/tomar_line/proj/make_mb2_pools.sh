#!/bin/zsh
# Two-step projected 4x4 seed pools from parents two projections away from <4,4,4> (2026-11-09):
#   Moosbauer <4,5,5>:76 over Z (matmul/external/mb455): kill one inner direction and one column, in both orders
#     (inner-a / inner-b on <4,5,5> then col on <4,4,5>; col on <4,5,5> then inner-a / inner-b on <4,5,4>);
#   Moosbauer <4,4,6>:74 over Z and the catalog's meta_flip_graph <4,4,6>:73 (matmul/external/mb446): kill two columns.
# Stage 1 keeps S1 projections per mode, stage 2 S2 per stage-1 seed (S2/2 per inner mode); project_f2.py checks every
# projection against its tensor; each pool is deduplicated by content.  The three parents build concurrently.
# usage: make_mb2_pools.sh OUTROOT [S1=40] [S2=25]   (pools land in OUTROOT/seeds444_{mb455,mb446,meta446})
set -u
export PYTHONHASHSEED=0
OUT=${1:?outroot}; S1=${2:-40}; S2=${3:-25}
M=/Users/greg/projects/logic/matmul
mkdir -p "$OUT"
proj() { # n1 n2 n3 in mode outdir max
  mkdir -p "$6"
  /usr/bin/python3 "$M/project_f2.py" "$1" "$2" "$3" "$4" --mode "$5" --out "$6" --max "$7" --quiet
}
collect() { # pool srcdir prefix
  local f
  mkdir -p "$1"
  for f in "$2"/*.bits(N); do cp "$f" "$1/${3}_$(basename "$f")"; done
}
dedupe() { # pool: drop files whose content repeats an earlier file
  local seen f h
  seen=$1/.seen; : > "$seen"
  for f in "$1"/*.bits(N); do h=$(md5 -q "$f"); if grep -q -x "$h" "$seen"; then rm "$f"; else echo "$h" >> "$seen"; fi; done
  rm -f "$seen"
}
report() { # pool
  echo "$(basename "$1"): $(ls "$1" | wc -l | tr -d ' ') seeds; ranks: $(ls "$1" | sed -E 's/.*proj444_([0-9]+)_.*/\1/' | sort -n | uniq -c | tr -s ' ' | tr '\n' ';')"
}
build455() {
  local P W POOL f b d mode
  P=$M/external/mb455/mb455_76_mod2.bits; W=$OUT/work_mb455; POOL=$OUT/seeds444_mb455; mkdir -p "$W" "$POOL"
  proj 4 5 5 "$P" inner-a "$W/s1_ia" "$S1"
  proj 4 5 5 "$P" inner-b "$W/s1_ib" "$S1"
  proj 4 5 5 "$P" col "$W/s1_col" "$S1"
  for f in "$W"/s1_ia/*.bits(N) "$W"/s1_ib/*.bits(N); do
    b=$(basename "$f" .bits); d=$(basename "$(dirname "$f")")
    proj 4 4 5 "$f" col "$W/s2_${d}_$b" "$S2"; collect "$POOL" "$W/s2_${d}_$b" "${d}_${b}_col"
  done
  for f in "$W"/s1_col/*.bits(N); do
    b=$(basename "$f" .bits)
    for mode in inner-a inner-b; do proj 4 5 4 "$f" "$mode" "$W/s2_col_${b}_$mode" $(( S2 / 2 )); collect "$POOL" "$W/s2_col_${b}_$mode" "col_${b}_$mode"; done
  done
  dedupe "$POOL"; report "$POOL"
}
build446() { # name parent
  local P W POOL f b
  P=$2; W=$OUT/work_$1; POOL=$OUT/seeds444_$1; mkdir -p "$W" "$POOL"
  proj 4 4 6 "$P" col "$W/s1_col" "$S1"
  for f in "$W"/s1_col/*.bits(N); do
    b=$(basename "$f" .bits)
    proj 4 4 5 "$f" col "$W/s2_$b" "$S2"; collect "$POOL" "$W/s2_$b" "col_${b}_col"
  done
  dedupe "$POOL"; report "$POOL"
}
build455 > "$OUT/build_mb455.log" 2>&1 &
build446 mb446 "$M/external/mb446/mb446_74_mod2.bits" > "$OUT/build_mb446.log" 2>&1 &
build446 meta446 "$M/external/mb446/meta446_73_mod2.bits" > "$OUT/build_meta446.log" 2>&1 &
wait
cat "$OUT"/build_*.log
