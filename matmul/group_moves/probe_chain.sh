#!/bin/zsh
# build the probe, collect visited states with the baseline engine, probe them
set -u
L=/Users/greg/projects/logic
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/move1
B=$L/target/release/flip
P=$L/target/release/group_probe
cd "$L" || exit 1
echo "=== build $(date '+%H:%M:%S')"
cargo build --release --bin group_probe --bin flip 2>&1 | grep -E "warning|error|Finished" || exit 1
mkdir -p "$S/states334" "$S/states444"
echo "=== collect <3,3,4> states (60 s, baseline engine) $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 150s "$B" 3 3 4 --trivial --save-at 30 --write-at 30 --record 29 --group-moves 0 --minutes 1 --threads 12 --seed 11 --out "$S/states334" --lift-below 0 > "$S/states334.log" 2>&1
echo "    exit $? $(tail -n 1 "$S/states334.log")"
echo "=== collect <4,4,4> states (45 s, baseline engine) $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 150s "$B" 4 4 4 --trivial --save-at 56 --write-at 56 --record 47 --group-moves 0 --minutes 0.75 --threads 12 --seed 11 --out "$S/states444" --lift-below 0 > "$S/states444.log" 2>&1
echo "    exit $? $(tail -n 1 "$S/states444.log")"
echo "=== probe <3,3,4> $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 900s "$P" 3 3 4 "$S/states334" --tries 3 --shuffles 200 --seek 100000 --threads 12 --max 6000 > "$S/probe334.log" 2>&1
echo "    exit $?"; cat "$S/probe334.log"
echo "=== probe <4,4,4> $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 900s "$P" 4 4 4 "$S/states444" --tries 3 --shuffles 200 --seek 100000 --threads 12 --max 3000 > "$S/probe444.log" 2>&1
echo "    exit $?"; cat "$S/probe444.log"
echo "=== probe chain done $(date '+%H:%M:%S')"
