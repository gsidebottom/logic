#!/bin/zsh
# Seeded 47-hunt: waits for today's ladders, then pursue10 with the
# pool preloaded from every verified dump in found48p (frontier 49,
# live bands above). 12 threads, 8 h. Kill: pkill -f pursue10
cd "$(dirname "$0")/.." || exit 1
while pgrep -f pursue10 >/dev/null; do sleep 120; done
echo "=== seeded overnight start $(date '+%m-%d %H:%M') ==="
./target/release/flip48p --prime f2 --pursue10 --dir matmul/mm64 \
  --poolseed matmul/found48p --plen 10000000 --threads 12 \
  --seconds 28800 --out matmul/found48p
echo "=== seeded overnight done $(date '+%m-%d %H:%M') ==="
