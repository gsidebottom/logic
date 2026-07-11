#!/bin/zsh
# Resume the flip48 campaigns after a reboot (or any interruption).
# Idempotent: skips arms that are already running or already complete.
# Loss model: only work INSIDE the in-flight unit is redone — the
# fringe re-runs at most the interrupted parents (fringe_done.txt is
# the sound completion log, H6), the chase re-runs at most the
# interrupted level (chase_frontier_L*.txt are full-beam dumps).
cd "$(dirname "$0")/.." || exit 1
BIN=./target/release/flip48
OUT=matmul/found48q

# --- fringe-exhaustive certificate arm ---
if pgrep -f "flip48 --pursue5" >/dev/null; then
  echo "fringe: already running"
elif grep -q "pursue5 done" matmul/fringe_exhaustive2.log; then
  echo "fringe: certificate complete — nothing to do"
else
  echo "fringe: resuming ($(tr -d ' ' <<<$(wc -l < $OUT/fringe_done.txt))/840 parents logged)"
  nohup $BIN --pursue5 0 --fringe-only --threads 8 --budget 7000000000 \
      --out $OUT --resume >> matmul/fringe_exhaustive2.log 2>&1 &
  disown
fi

# --- gradient-chase arm (budget is per-launch: ~2 levels at L8+ scale) ---
if pgrep -f "flip48 --pursue6" >/dev/null; then
  echo "chase: already running"
else
  PICK=$(ls $OUT/chase_frontier_L*.txt | sed 's/.*_L\([0-9]*\)\.txt/\1 &/' | sort -n | tail -1)
  N=${PICK%% *}; FILE=${PICK#* }
  echo "chase: resuming from level $N frontier ($FILE)"
  nohup $BIN --pursue6 --beam 1500 --samples 60 --depth 12 \
      --budget 2500000000 --threads 6 --resume6 "$FILE" --startlevel "$N" \
      --out $OUT >> matmul/chase2.log 2>&1 &
  disown
fi
echo "watch with: tail -f matmul/fringe_exhaustive2.log matmul/chase2.log"
