#!/bin/zsh
# HKS-corpus rediscovery campaign — RESTARTABLE.
#   Usage: run_rediscovery.sh [threads] [target] [chunk-minutes]
# Waits for the rank-22 flip23p arms (storm23_overnight parents) to
# exit, then runs walk.py in chunks from the 4-classic seed pool.
# Durability: walk.py archives every find on landing and rebuilds its
# pool from seeds+archive at startup, so killing this at ANY point
# loses at most one in-flight 15-second anf run.  Re-running this
# script resumes exactly where it left off (it also skips the wait if
# the arms are already gone).
#   Stop:   pkill -f run_rediscovery.sh; pkill -f 'walk.py'
#           (orphaned anf runs self-expire within 15 s)
#   Resume: nohup matmul/replica4/run_rediscovery.sh >> matmul/replica4/campaign.log &
cd "$(dirname "$0")/.." || exit 1          # -> matmul/ (walk.py cwd)
THREADS=${1:-12}
TARGET=${2:-13000}
CHUNK=${3:-30}
echo "=== rediscovery launcher up $(date '+%m-%d %H:%M'); waiting for rank-22 arms ==="
while pgrep -f storm23_overnight >/dev/null; do sleep 300; done
echo "=== arms done $(date '+%m-%d %H:%M'); walking at $THREADS threads, target $TARGET, ${CHUNK}m chunks ==="
i=0
while true; do
  n=$(ls replica4/found 2>/dev/null | grep -c '\.bits$')
  echo "=== chunk $i  archive $n schemes  $(date '+%m-%d %H:%M') ==="
  if [ "$n" -ge "$TARGET" ]; then
    echo "=== TARGET $TARGET reached $(date '+%m-%d %H:%M') ==="
    break
  fi
  python3 walk.py --minutes "$CHUNK" --nfix 300 --runs 8 \
    --threads "$THREADS" --rng $((100 + i)) \
    --seeds replica4/seeds --archive replica4/found 2>&1 | tail -2
  i=$((i + 1))
done
