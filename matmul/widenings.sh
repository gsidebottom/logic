#!/bin/zsh
# Cost-ordered widenings (2026-07-13), after day-2's negatives:
#   A. BabyBear 4x4 repair ladder k=3..6   (~25 min)
#   B. 3x3 Goldilocks repair k=3..9 for ALL 30 census seeds (~2 h)
#      — rigidity is seed-specific; day-2 only tested mm23.
#   C. 4x4 Goldilocks repair k=7, 73.6M subsets (~3.5 h)
#   D. m31 3x3 pursue7 arm, top-10 seeds x 1200 s (~3.3 h)
# All RECORDP-alarmed; log = matmul/widenings.log.
cd "$(dirname "$0")/.." || exit 1
T=${1:-12}
B23=./target/release/flip23p
B48=./target/release/flip48p
echo "=== widenings start $(date '+%m-%d %H:%M')  threads $T ==="
echo "--- A: 4x4 babybear repair k=3..6 ---"
for K in 3 4 5 6; do
  echo "-- A k=$K  $(date '+%H:%M')"
  $B48 --prime babybear --repair "$K" --threads "$T" --seconds 7200 \
       --out matmul/found48p 2>&1 | tail -2
done
echo "--- B: 3x3 goldilocks repair k=3..9 x 30 census seeds ---"
grep -v '^#' matmul/seeds23/SHORTLIST.txt | while read -r d rest; do
  [ -z "$d" ] && continue
  echo "-- B seed $(basename "$d")  $(date '+%H:%M')"
  for K in 3 4 5 6 7 8 9; do
    $B23 --dir "$d" --repair "$K" --threads "$T" --seconds 1800 \
         --out matmul/found23p 2>&1 | grep "repair k="
  done
done
echo "--- C: 4x4 goldilocks repair k=7 (73.6M)  $(date '+%H:%M') ---"
$B48 --repair 7 --threads "$T" --seconds 28800 \
     --out matmul/found48p 2>&1 | tail -2
echo "--- D: m31 3x3 pursue7 arm, top-10 x 1200 s  $(date '+%H:%M') ---"
mkdir -p matmul/found23p/m31
grep -v '^#' matmul/seeds23/SHORTLIST.txt | head -10 | while read -r d rest; do
  [ -z "$d" ] && continue
  echo "== D m31 $(basename "$d")  $(date '+%H:%M')"
  $B23 --prime m31 --dir "$d" --seconds 1200 --threads "$T" \
       --out matmul/found23p/m31 --pursue7 --hi 26 --mix 2500 \
       2>&1 | tail -3
done
echo "=== widenings complete $(date '+%m-%d %H:%M') ==="
echo "RECORDP files:"
ls matmul/found23p/RECORDP* matmul/found23p/m31/RECORDP* \
   matmul/found48p/RECORDP* 2>/dev/null | wc -l
