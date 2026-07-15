#!/bin/zsh
# n=256 rank-48 retry (matlv 3,4 — depth-appropriate materialization
# after matlv 0,2 died to OOM at depth 4) + full-scenario runs.
# RSS guard: kill any benchzk exceeding CAP_GB (record the event) so a
# dense config can never swap-storm the machine again.
set -u
cd "$(dirname $0)"
B=./target/release/benchzk
CAP_GB=${CAP_GB:-26}
RES=n256_results.txt
FULL=fullscen_results.txt

guarded() {
  "$@" &
  local pid=$!
  while kill -0 $pid 2>/dev/null; do
    local rss_kb=$(ps -o rss= -p $pid 2>/dev/null | tr -d ' ')
    if [ -n "$rss_kb" ] && [ "$rss_kb" -gt $(( CAP_GB * 1024 * 1024 )) ]; then
      echo "RSS-GUARD: killed '$*' at $(( rss_kb / 1024 / 1024 )) GB (cap ${CAP_GB} GB)"
      kill -9 $pid
      wait $pid 2>/dev/null
      return 137
    fi
    sleep 10
  done
  wait $pid
}

{
  echo "--- retry $(date): matlv 3 then 4, RSS cap ${CAP_GB} GB ---"
  guarded $B 256 rank48 --matlv 3 --prove
  guarded $B 256 rank48 --matlv 4 --prove
} >> $RES 2>&1

{
  echo "=== full zk scenario table $(date) ==="
  guarded $B 64 naive --full
  guarded $B 64 rank48 --matlv 2 --full
  guarded $B 256 naive --full
  guarded $B 256 rank48 --matlv 3 --full
} > $FULL 2>&1

echo "CHAIN DONE $(date)"
