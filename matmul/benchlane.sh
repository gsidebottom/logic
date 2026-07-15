#!/bin/zsh
# benchlane — sequential zk-proof benchmark program (~6 cores):
#  1. Goldilocks NTT curve (gated) 2^14..2^25
#  2. BN254-Fr NTT curve 2^14..2^25 (arkworks domains)
#  3. Groth16 n=64 --full phase tables: naive, strassen, rank48
#     matlv 0..3 (RAYON capped at 6, RSS-guarded)
#  4. First measured n=4096 witness-gen A/B: bench284r vs bench315r
set -u
cd /Users/greg/projects/logic
CAP_GB=48
guarded() {
  "$@" &
  local pid=$!
  while kill -0 $pid 2>/dev/null; do
    local rss_kb=$(ps -o rss= -p $pid 2>/dev/null | tr -d ' ')
    if [ -n "$rss_kb" ] && [ "$rss_kb" -gt $(( CAP_GB * 1024 * 1024 )) ]; then
      echo "RSS-GUARD: killed '$*' at $(( rss_kb / 1024 / 1024 )) GB"
      kill -9 $pid; wait $pid 2>/dev/null; return 137
    fi
    sleep 10
  done
  wait $pid
}
echo "=== BENCHLANE START $(date) ==="
echo "--- [1/5] Goldilocks NTT curve ---"
./target/release/benchntt_g 25
echo "--- [2/5] BN254-Fr NTT curve ---"
./matmul/benchzk/target/release/benchzk 25 ntt
echo "--- [3/5] n=256 retry at 48 GB cap (64 GB machine; prior 26 GB guard was wrong) ---"
B=./matmul/benchzk/target/release/benchzk
export RAYON_NUM_THREADS=6
guarded $B 256 rank48 --matlv 3 --prove
guarded $B 256 rank48 --matlv 4 --prove
guarded $B 256 rank48 --matlv 2 --prove
guarded $B 256 naive --full
guarded $B 256 rank48 --matlv 3 --full
echo "--- [4/5] Groth16 n=64 full-scenario sweep ---"
guarded $B 64 naive --full
guarded $B 64 strassen --full
for lv in 0 1 2 3; do
  guarded $B 64 rank48 --matlv $lv --full
done
echo "--- [5/5] n=4096 witness-gen A/B (284 vs 315) ---"
BENCH_BIG=1 ./target/release/bench284r
BENCH_BIG=1 ./target/release/bench315r
echo "=== BENCHLANE DONE $(date) ==="
