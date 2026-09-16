#!/bin/bash
# The box engine's refutations, certified end to end (doc/box_backend_design.md §4):
#
#   sat -b boxes --proof  ->  drat-trim (verify + elaborate to LRAT)  ->  cake_lpr
#
# Usage: tools/boxes_certify_corpus.sh DIR [TIMEOUT_S]
#
# Every `*.cnf` in DIR is refuted and checked against itself.  A boxed
# instance is declared instead by a line in DIR/boxed.list:
#
#   NAME  INPUT.cnf  TARGET.cnf  BOXES.json  SOURCE.cnf
#
# where INPUT is what the engine is given (the residual), SOURCE the clauses
# the boxes stand for and TARGET their concatenation — the original formula
# the proof certifies.  `cnf2boxes.py` writes residual.cnf, boxes.json and
# absorbed.cnf, so TARGET is `cat residual.cnf absorbed.cnf`.
set -u
DIR=${1:?usage: boxes_certify_corpus.sh DIR [TIMEOUT_S]}
T=${2:-800}
SAT=${SAT:-$(cd "$(dirname "$0")/.." && pwd)/target/release/sat}
cd "$DIR" || exit 2
now() { python3 -c 'import time;print(time.time())'; }

row() {  # name, input cnf, formula the proof is checked against, extra sat args
  local n="$1" inp="$2" target="$3"; shift 3
  local t0 t1 t2 t3 t4 out v sz tr ck lem
  t0=$(now); out=$(timeout $((T + 100)) "$SAT" -b boxes --timeout "$T" --proof "$n.drat" "$@" < "$inp" 2>&1); t1=$(now)
  v=$(echo "$out" | grep -oE "^s (SATISFIABLE|UNSATISFIABLE)" | head -1 | awk '{print $2}'); [ -z "$v" ] && v=TIMEOUT
  lem=$(echo "$out" | grep -oE "[0-9]+ box lemmas derived" | grep -oE "^[0-9]+"); [ -z "$lem" ] && lem=0
  if [ "$v" != UNSATISFIABLE ]; then
    printf "%-34s %-6s %8.2f %11s %8s %8s %8s %s\n" "$n" "$v" "$(echo "$t1-$t0" | bc)" - - - - -
    rm -f "$n.drat"; return
  fi
  sz=$(wc -c < "$n.drat" | tr -d ' ')
  t2=$(now); tr=$(timeout 5000 drat-trim "$target" "$n.drat" -L "$n.lrat" 2>&1 | grep -c "s VERIFIED"); t3=$(now)
  ck=$(timeout 5000 cake_lpr "$target" "$n.lrat" 2>&1 | grep -c "VERIFIED UNSAT"); t4=$(now)
  printf "%-34s %-6s %8.2f %11s %8.2f %8.2f %8s %s\n" "$n" UNSAT "$(echo "$t1-$t0" | bc)" "$sz" \
         "$(echo "$t3-$t2" | bc)" "$(echo "$t4-$t3" | bc)" "$lem" \
         "$([ "$tr" -ge 1 ] && echo trim=ok || echo trim=FAIL),$([ "$ck" -ge 1 ] && echo cake=ok || echo cake=FAIL)"
  rm -f "$n.drat" "$n.lrat"
}

printf "%-34s %-6s %8s %11s %8s %8s %8s %s\n" instance verdict solve_s proof_B trim_s cake_s lemmas checkers
boxed_inputs=""
if [ -f boxed.list ]; then
  while read -r name inp target boxes source; do
    [ -z "${name:-}" ] && continue
    case "$name" in '#'*) continue ;; esac
    boxed_inputs="$boxed_inputs $inp $target $source"
    row "$name" "$inp" "$target" --boxes "$boxes" --boxes-source "$source"
  done < boxed.list
fi
for f in *.cnf; do
  [ -e "$f" ] || continue
  case " $boxed_inputs " in *" $f "*) continue ;; esac   # an input or a source named by boxed.list
  row "${f%.cnf}" "$f" "$f"
done
echo CORPUS EXIT
