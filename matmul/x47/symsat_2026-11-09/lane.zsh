#!/bin/zsh
# lane.zsh LANEFILE OUTDIR [CAP]: sequential equal-budget arms on one core.  Lines: label kind(plain|lex|hydra) shape-spec
set -u
LANE=$1; OUT=$2; CAP=${3:-1200}
H=/Users/greg/projects/logic/matmul/x47
SAT=/Users/greg/projects/logic/target/release/sat
mkdir -p "$OUT/cnf"
while read -r label kind spec; do
  [[ -z "$label" ]] && continue
  f="$OUT/cnf/${label}_${kind}.cnf"
  if [[ "$kind" == lex ]]; then /usr/bin/python3 "$H/hcnf.py" --group d8 --shape "$spec" --lex "$f" > /dev/null
  else /usr/bin/python3 "$H/hcnf.py" --group d8 --shape "$spec" "$f" > /dev/null; fi
  t0=$(date +%s)
  if [[ "$kind" == hydra ]]; then
    /opt/homebrew/bin/timeout $(( CAP + 60 )) "$SAT" -b hydra -t $CAP < "$f" > "$OUT/${label}_${kind}.out" 2>&1; rc=$?
    v="rc$rc $(grep -m1 '^s ' "$OUT/${label}_${kind}.out" | tr -d '\n')"
  else
    /opt/homebrew/bin/timeout $CAP cadical --seed=100 -q "$f" > "$OUT/${label}_${kind}.out" 2>&1; rc=$?
    case $rc in 10) v=SAT;; 20) v=UNSAT;; *) v="timeout/rc$rc";; esac
  fi
  dt=$(( $(date +%s) - t0 ))
  echo "$(date '+%H:%M:%S') $label $kind $spec -> $v in ${dt}s" >> "$OUT/lane.log"
  if [[ $rc -eq 10 && "$kind" != hydra ]]; then
    /usr/bin/python3 "$H/hcnf.py" --group d8 --shape "$spec" decode "$OUT/${label}_${kind}.out" "$OUT/${label}_${kind}.bits" >> "$OUT/lane.log" 2>&1
  fi
done < "$LANE"
echo "$(date '+%H:%M:%S') lane $LANE done" >> "$OUT/lane.log"
