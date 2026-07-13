#!/bin/zsh
# rank-22 / rank-47 day-2 portfolio (2026-07-13):
#   1. 3x3 repair ladder k=5..9, Goldilocks then BabyBear (exhaustive
#      C(23,k) sweeps; any completion = verified rank <= 22).
#   2. 4x4 repair ladder k=5, k=6 over Goldilocks (C(48,5)=1.7M,
#      C(48,6)=12.3M; any completion = verified rank 47).
#   3. hi-30 deep-band pursue7 arm, top-10 census seeds x 1200 s
#      (tests the "22 sits behind a higher ridge" hypothesis).
# All stages RECORDP-alarmed; log = matmul/rank22_day2.log.
cd "$(dirname "$0")/.." || exit 1
B23=./target/release/flip23p
B48=./target/release/flip48p
T=${1:-12}
echo "=== day2 start $(date '+%m-%d %H:%M')  threads $T ==="
for K in 5 6 7 8 9; do
  echo "--- 3x3 goldilocks repair k=$K  $(date '+%H:%M') ---"
  $B23 --repair "$K" --threads "$T" --seconds 3600 \
       --out matmul/found23p 2>&1 | tail -3
done
for K in 5 6 7 8 9; do
  echo "--- 3x3 babybear repair k=$K  $(date '+%H:%M') ---"
  $B23 --prime babybear --repair "$K" --threads "$T" --seconds 3600 \
       --out matmul/found23p 2>&1 | tail -3
done
echo "--- 4x4 goldilocks repair k=5  $(date '+%H:%M') ---"
$B48 --repair 5 --threads "$T" --seconds 7200 \
     --out matmul/found48p 2>&1 | tail -3
echo "--- 4x4 goldilocks repair k=6  $(date '+%H:%M') ---"
$B48 --repair 6 --threads "$T" --seconds 14400 \
     --out matmul/found48p 2>&1 | tail -3
echo "--- hi-30 arm: top-10 seeds x 1200 s  $(date '+%H:%M') ---"
mkdir -p matmul/found23p/p7g30
grep -v '^#' matmul/seeds23/SHORTLIST.txt | head -10 | while read -r d rest; do
  [ -z "$d" ] && continue
  echo "=== hi30 $(basename "$d")  [$rest]  $(date '+%H:%M') ==="
  $B23 --dir "$d" --seconds 1200 --threads "$T" \
       --out matmul/found23p/p7g30 --pursue7 --hi 30 --mix 2500 \
       2>&1 | tail -3
done
echo "=== day2 complete $(date '+%m-%d %H:%M') ==="
echo "RECORDP files:"
ls matmul/found23p/RECORDP* matmul/found23p/p7g30/RECORDP* \
   matmul/found48p/RECORDP* 2>/dev/null | wc -l
