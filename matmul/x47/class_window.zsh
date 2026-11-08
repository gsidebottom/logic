#!/bin/zsh
# The +4 orbit-window pipeline for one rank-47 class, from scratch (2026-11-08; the recipe that found the 166):
#   usage: class_window.zsh CLASS [THREADS]        run from matmul/x47; needs seeds/CLASS_{L,R,P}.sms
# 1. scan: fresh side tables at ONE Boyar-Peralta run per entry (--runs 1; without it the default 2000 runs per
#    entry make the three 840x840 tables ~2000x slower and the log stays empty for hours), +4 window, tables saved
#    to out/scan4_CLASS/scan_tables.u8 for re-emission with `scan --tables`.
# 2. refine: BP 1000 runs + bottom-up exact per side (cap 30 s) on every candidate triple.
# 3. targeted settle first: the triples at the refine's best and best+1 (the ones that can beat the record cheaply),
#    depth 12, cap 600 s; it prints IMPROVED when a side's exact value lowers a total below the refine's best.
# 4. then the full window at --target (best found), depth 8 cap 600 and depth 12 cap 60/600, sharing the side cache.
# 5. on IMPROVED: `refine --cap 1800` on that triple alone emits the programs; check with x47check.py and SLPchecker.
set -u
c=${1:?class}; THR=${2:-12}
L=/Users/greg/projects/logic; B=$L/target/release/xor47; T=/opt/homebrew/bin/timeout
stamp() { echo "=== $1 $(date '+%H:%M:%S')"; }
[ -f "seeds/${c}_L.sms" ] || { echo "seeds/${c}_L.sms missing"; exit 1; }
if [ ! "$B" -nt "$L/src/bin/xor47.rs" ]; then echo "xor47 binary older than its source: ABORT"; exit 1; fi
stamp "$c: fresh scan, +4 window, BP x1"
$T 14400s "$B" scan "seeds/$c" --runs 1 --depth 4 --threads $THR --out "out/scan4_$c" > "out/scan4_$c.log" 2>&1
echo "    exit $?"; grep -E 'orbit minimum|wrote' "out/scan4_$c.log" | cut -c1-160
stamp "$c: refine"
$T 21600s "$B" refine "seeds/$c" "out/scan4_$c/scan_cands.txt" --runs 1000 --cap 30 --threads $THR --out "out/scanref4_$c" > "out/scanref4_$c.log" 2>&1
echo "    exit $?"; grep -E '^best' "out/scanref4_$c.log" | cut -c1-120
best=$(grep -E '^best' "out/scanref4_$c.log" | awk '{print $2}')
grep -E "^point .* -> total ($best|$((best + 1)))( |\$)" "out/scanref4_$c.log" > "out/scanref4_${c}_top.log"
stamp "$c: targeted settle of the $(wc -l < "out/scanref4_${c}_top.log") triples at $best and $((best + 1)), depth 12 cap 600"
$T 21600s "$B" settle "seeds/$c" "out/scanref4_${c}_top.log" --depth 12 --cap 600 --threads $THR --out "out/settle_top_$c" > "out/settle_top_$c.log" 2>&1
echo "    exit $?"; grep -vE '^(side|  point)' "out/settle_top_$c.log" | tail -n 3 | cut -c1-200
tgt=$(grep -E '^best total' "out/settle_top_$c.log" | awk '{print $3}' | tr -d ';'); [ -n "$tgt" ] || tgt=$best
mkdir -p "out/settle4_$c"; cat "out/settle_top_$c/settled_sides.txt" >> "out/settle4_$c/settled_sides.txt" 2>/dev/null; sort -u -o "out/settle4_$c/settled_sides.txt" "out/settle4_$c/settled_sides.txt"
stamp "$c: full window at target $tgt, depth 8 cap 600"
$T 21600s "$B" settle "seeds/$c" "out/scanref4_$c.log" --depth 8 --cap 600 --target $tgt --threads $THR --out "out/settle4_$c" > "out/settle4_$c.log" 2>&1
echo "    exit $?"; grep -vE '^(side|  point)' "out/settle4_$c.log" | tail -n 2 | cut -c1-200
stamp "$c: full window at target $tgt, depth 12 cap 60"
$T 21600s "$B" settle "seeds/$c" "out/scanref4_$c.log" --depth 12 --cap 60 --target $tgt --threads $THR --out "out/settle4_$c" > "out/settle4b_$c.log" 2>&1
echo "    exit $?"; grep -vE '^(side|  point)' "out/settle4b_$c.log" | tail -n 2 | cut -c1-200
stamp "$c done; open points: $(grep -c '^point' "out/settle4_$c/settle_open.txt" 2>/dev/null)"
