#!/bin/zsh
# F_2 persistent-walk reproduction (Kauers-Moosbauer protocol shape):
# long plateau walks (--mix 300000) then quench, both dimensions.
#   arm 1: 4x4 from Strassen^2 49 -> hunt 48/47 mod 2 (known to exist)
#   arm 2: 3x3 from mm23        -> hunt 22 mod 2 (open)
# Waits for the widenings batch to release cores. Kill anytime:
#   pkill -f f2_overnight.sh; pkill -f "prime f2"
cd "$(dirname "$0")/.." || exit 1
while pgrep -f widenings.sh >/dev/null; do sleep 300; done
echo "=== f2 overnight start $(date '+%m-%d %H:%M') ==="
./target/release/flip48p --prime f2 --pursue7 --hi 50 --mix 300000 \
  --threads 6 --seconds 21600 --out matmul/found48p >> matmul/f2_48.log 2>&1 &
./target/release/flip23p --prime f2 --pursue7 --hi 26 --mix 300000 \
  --threads 6 --seconds 21600 --out matmul/found23p/f2 >> matmul/f2_23.log 2>&1 &
wait
echo "=== f2 overnight done $(date '+%m-%d %H:%M') ==="
ls matmul/found48p/RECORDP* matmul/found23p/f2/RECORDP* 2>/dev/null | wc -l
