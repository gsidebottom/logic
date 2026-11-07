#!/bin/zsh
# after move 3: lib tests (flip_group), sampled plane probes with the staged bound and the SAT oracle, then move 2
# usage: probe3_chain.sh [MAX334=0 (all)] [MAX444=0 (all)] [PAR2=8] [TO2=600]
set -u
MAX334=${1:-0}; MAX444=${2:-0}; PAR2=${3:-8}; TO2=${4:-600}
M334=""; [ "$MAX334" -gt 0 ] && M334="--max $MAX334"
M444=""; [ "$MAX444" -gt 0 ] && M444="--max $MAX444"
L=/Users/greg/projects/logic
S=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
P=$L/target/release/group_probe
cd "$L" || exit 1
echo "=== tests $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 1200s cargo test --release --lib flip_group -- --nocapture 2>&1 | grep -E "^test |test result|panicked|gap|checked|excess"
echo "    exit ${pipestatus[1]}"
mkdir -p "$S/move1/cnf"
echo "=== probe <3,3,4> planes, states ${MAX334:-all} $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 2700s "$P" 3 3 4 "$S/move1/states334" ${=M334} --tries 3 --shuffles 200 --seek 100000 --threads 12 --seed 7 --tmp "$S/move1/cnf" --sat-timeout 10 --sat-max 24 > "$S/move1/probe334_planes2.log" 2>&1
echo "    exit $?"; cat "$S/move1/probe334_planes2.log"
echo "=== probe <4,4,4> planes, states ${MAX444:-all} $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 2700s "$P" 4 4 4 "$S/move1/states444" ${=M444} --tries 3 --shuffles 200 --seek 100000 --threads 12 --seed 7 --tmp "$S/move1/cnf" --sat-timeout 10 --sat-max 24 > "$S/move1/probe444_planes2.log" 2>&1
echo "    exit $?"; cat "$S/move1/probe444_planes2.log"
echo "=== move 2: CaDiCaL campaign, $PAR2 parallel, $TO2 s each $(date '+%H:%M:%S')"
/opt/homebrew/bin/timeout 5400s /bin/zsh "$S/move2/run_move2.sh" $TO2 $PAR2 > "$S/move2/runs/m2_chain.log" 2>&1
echo "    exit $?"; cat "$S/move2/runs/m2_chain.log"
echo "=== probe3 chain done $(date '+%H:%M:%S')"
