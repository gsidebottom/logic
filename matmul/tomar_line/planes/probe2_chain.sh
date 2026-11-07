#!/bin/zsh
# build, test, then probe both state sets with the plane moves and the SAT oracle
set -u
L=/Users/greg/projects/logic
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/move1
P=$L/target/release/group_probe
cd "$L" || exit 1
echo "=== build $(date '+%H:%M:%S')"
cargo build --release --bin flip --bin group_probe 2>&1 | grep -E "^(warning|error)|-->|Finished" || exit 1
echo "=== tests $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 600s cargo test --release --lib flip -- --nocapture 2>&1 | grep -E "^test |test result|panicked|gap|checked" 
echo "=== probe <3,3,4> with planes $(date '+%H:%M:%S')"
mkdir -p "$S/cnf"
/opt/homebrew/bin/timeout 1500s "$P" 3 3 4 "$S/states334" --tries 3 --shuffles 200 --seek 100000 --threads 12 --tmp "$S/cnf" --sat-timeout 20 > "$S/probe334_planes.log" 2>&1
echo "    exit $?"; cat "$S/probe334_planes.log"
echo "=== probe <4,4,4> with planes $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 2400s "$P" 4 4 4 "$S/states444" --tries 3 --shuffles 200 --seek 100000 --threads 12 --tmp "$S/cnf" --sat-timeout 20 > "$S/probe444_planes.log" 2>&1
echo "    exit $?"; cat "$S/probe444_planes.log"
echo "=== probe chain done $(date '+%H:%M:%S')"
