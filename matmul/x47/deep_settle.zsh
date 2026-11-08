#!/bin/zsh
# deep_settle.zsh CLASS DEPTH [THREADS] [NICE] -- run from matmul/x47.
# Re-settle a class's +4-window refine log (out/scanref4_CLASS.log, side cache out/settle4_CLASS) at helper
# depth DEPTH in two stages: cap 60 s (the top-level test times out fast where it is hopeless and the
# bottom-up pass raises the floors), then, if points stay open below the class best, cap 600 s on those
# sides only (open sides pruned from the cache, backup settled_sides.cap60.txt kept).  The queue's
# `settle --depth 8` skips sides whose BP program sits 9 or more helpers above the target count, which
# is what left 25 km47 points open on 2026-11-07; depth 10 closed them in 92 s.
set -u
c=$1; d=$2; THR=${3:-12}; NICE=${4:-0}
B=${XOR47:-../../target/release/xor47}; T=/opt/homebrew/bin/timeout
stamp() { echo "=== $1 $(date '+%H:%M:%S')"; }
o=out/settle4_$c
if [ ! -f "out/scanref4_$c.log" ]; then echo "$c: no +4 refine log, skipped"; exit 0; fi
stamp "$c: deep settle depth $d cap 60"
nice -n $NICE $T 7200s "$B" settle "seeds/$c" "out/scanref4_$c.log" --depth $d --cap 60 --threads $THR --out "$o" > "out/settle4b_$c.log" 2>&1
echo "    exit $?"; grep -E 'open sides|points still open' "out/settle4b_$c.log" | tail -n 2 | cut -c1-200
open=$(grep -oE 'points still open below it: [0-9]+' "out/settle4b_$c.log" | tail -n 1 | grep -oE '[0-9]+$')
if [ -n "$open" ] && [ "$open" -gt 0 ]; then
  cp "$o/settled_sides.txt" "$o/settled_sides.cap60.txt"
  awk '$2 == $3' "$o/settled_sides.cap60.txt" > "$o/settled_sides.txt"
  echo "    cache: kept $(wc -l < "$o/settled_sides.txt") exact sides of $(wc -l < "$o/settled_sides.cap60.txt"); open ones retried"
  stamp "$c: deep settle depth $d cap 600 ($open points open)"
  nice -n $NICE $T 21600s "$B" settle "seeds/$c" "out/scanref4_$c.log" --depth $d --cap 600 --threads $THR --out "$o" > "out/settle4c_$c.log" 2>&1
  echo "    exit $?"; grep -E 'open sides|points still open' "out/settle4c_$c.log" | tail -n 2 | cut -c1-200
fi
echo "    open points now: $(grep -c '^point' "$o/settle_open.txt" 2>/dev/null)"
