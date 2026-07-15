#!/bin/zsh
# benchlane2 — salvage after the matlv3 swap balloon (RSS 14 GB but
# 190+ GB footprint, swap nearly exhausted; RSS-only guarding is
# blind to macOS swap/compression). Guard v2 kills on RSS > 44 GB OR
# swap growth > 8 GB over launch baseline. Dropped as proven bombs:
# n=256 rank48 matlv 2 and 3 (folded depth-4 density needs >>64 GB).
set -u
cd /Users/greg/projects/logic
CAP_GB=44
SWAP_GROW_MB=8192
swap_used_mb() { sysctl -n vm.swapusage | awk '{print int($6)}'; }
BASE_SWAP=$(swap_used_mb)
guarded() {
  "$@" &
  local pid=$!
  while kill -0 $pid 2>/dev/null; do
    local rss_kb=$(ps -o rss= -p $pid 2>/dev/null | tr -d ' ')
    local sw=$(swap_used_mb)
    if { [ -n "$rss_kb" ] && [ "$rss_kb" -gt $(( CAP_GB * 1024 * 1024 )) ]; } \
       || [ $(( sw - BASE_SWAP )) -gt $SWAP_GROW_MB ]; then
      echo "GUARD-V2: killed '$*' (rss $(( ${rss_kb:-0} / 1024 / 1024 )) GB, swap +$(( sw - BASE_SWAP )) MB)"
      kill -9 $pid; wait $pid 2>/dev/null
      sleep 20  # let swap drain before the next run
      BASE_SWAP=$(swap_used_mb)
      return 137
    fi
    sleep 10
  done
  wait $pid
}
B=./matmul/benchzk/target/release/benchzk
echo "=== BENCHLANE2 START $(date) (swap baseline ${BASE_SWAP} MB) ==="
echo "--- [1/4] BN254-Fr NTT curve, single-thread (fair vs Goldilocks) ---"
RAYON_NUM_THREADS=1 $B 22 ntt
echo "--- [2/4] n=256: the two configs with a real memory profile ---"
export RAYON_NUM_THREADS=6
guarded $B 256 rank48 --matlv 4 --prove
guarded $B 256 naive --full
echo "--- [3/4] Groth16 n=64 full-scenario sweep ---"
guarded $B 64 naive --full
guarded $B 64 strassen --full
for lv in 0 1 2 3; do
  guarded $B 64 rank48 --matlv $lv --full
done
echo "--- [4/4] n=4096 witness-gen A/B (284 vs 315) ---"
BENCH_BIG=1 ./target/release/bench284r
BENCH_BIG=1 ./target/release/bench315r
echo "=== BENCHLANE2 DONE $(date) ==="
