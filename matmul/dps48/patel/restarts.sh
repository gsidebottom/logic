#!/bin/bash
# Restart campaign with the Rust LNS: many naive (matrix-only) seeds per side,
# short budgets; then the best program per side is verified with SLPchecker
# and the triple with slp48check.py.
#   restarts.sh PREFIX OUTDIR [SEEDS=12] [WALL=180] [SEED0=100]
# PREFIX_{L,R,P}.sms must exist; P is searched through its transpose.
set -u
PREFIX=$1; OUT=$2; SEEDS=${3:-12}; WALL=${4:-180}; SEED0=${5:-100}
ROOT=$(cd "$(dirname "$0")/../../.." && pwd)
LNS=${LNS48_BIN:-$ROOT/target/release/lns48}
BIN=${PLINOPT_BIN:-/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/plinopt-run/bin}
mkdir -p "$OUT"
$BIN/matrix-transpose "${PREFIX}_P.sms" > "$OUT/Pt.sms"
sms_for() { case $1 in L) echo "${PREFIX}_L.sms";; R) echo "${PREFIX}_R.sms";; Pt) echo "$OUT/Pt.sms";; esac; }
for side in L R Pt; do
  echo "== $side: $SEEDS naive seeds x ${WALL}s $(date +%H:%M:%S)"
  $LNS --sms "$(sms_for $side)" --out "$OUT/$side" --wall "$WALL" --seeds "$SEEDS" --seed "$SEED0" --log 1000000 2>&1 | grep -E '^final' | cut -c1-160
done
# assemble: L, R as emitted; P = transposed P^T program
cp "$OUT/L/best.slp" "$OUT/L.slp"; cp "$OUT/R/best.slp" "$OUT/R.slp"
$BIN/transpozer < "$OUT/Pt/best.slp" 2>/dev/null | grep -v '^#' > "$OUT/P.slp"
for side in L R P; do
  printf '%s SLPchecker: ' $side
  $BIN/SLPchecker -M "${PREFIX}_$side.sms" < "$OUT/$side.slp" 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | grep -oE 'SUCCESS[^<]*<[0-9]+, [0-9]+>|ERROR.*' | head -1
done
python3 "$ROOT/matmul/dps48/slp48check.py" --dir "$OUT" | tail -2
