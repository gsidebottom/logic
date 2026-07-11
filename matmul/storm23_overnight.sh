#!/bin/zsh
# Overnight flip23 storm portfolio over the census shortlist.
# Usage: storm23_overnight.sh [secs-per-seed] [threads] [outdir] [extra flags...]
#   e.g. storm23_overnight.sh 600 7 matmul/found23q/d40 --maxd 40
# Random split/flip/reduce walks (rank cap 27) from each of the 30
# census-selected seeds; any verified rank <= 22 is dumped + screamed
# (world record); distinct rank-23 landings are collected for the
# novelty pool (new classes reopen the 54-adds hunt).
cd "$(dirname "$0")/.." || exit 1
BIN=./target/release/flip23
SECS=${1:-900}
THREADS=${2:-8}
OUT=${3:-matmul/found23q}
if [ $# -ge 3 ]; then shift 3; else shift $#; fi
mkdir -p "$OUT"
grep -v '^#' matmul/seeds23/SHORTLIST.txt | while read -r d rest; do
  [ -z "$d" ] && continue
  echo "=== storm $(basename $d)  [$rest]  $(date '+%H:%M') ==="
  $BIN --dir "$d" --seconds "$SECS" --threads "$THREADS" \
       --out "$OUT" "$@" 2>&1 | tail -3
done
echo "=== storm portfolio complete $(date '+%H:%M') ==="
