#!/bin/zsh
# Overnight flip23 storm portfolio over the census shortlist.
# Usage: storm23_overnight.sh [secs-per-seed] [threads]
# Random split/flip/reduce walks (rank cap 27) from each of the 30
# census-selected seeds; any verified rank <= 22 is dumped + screamed
# (world record); distinct rank-23 landings are collected for the
# novelty pool (new classes reopen the 54-adds hunt).
cd "$(dirname "$0")/.." || exit 1
BIN=./target/release/flip23
SECS=${1:-900}
THREADS=${2:-8}
mkdir -p matmul/found23q
grep -v '^#' matmul/seeds23/SHORTLIST.txt | while read -r d rest; do
  [ -z "$d" ] && continue
  echo "=== storm $(basename $d)  [$rest]  $(date '+%H:%M') ==="
  $BIN --dir "$d" --seconds "$SECS" --threads "$THREADS" \
       --out matmul/found23q 2>&1 | tail -3
done
echo "=== storm portfolio complete $(date '+%H:%M') ==="
