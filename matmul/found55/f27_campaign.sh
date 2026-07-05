#!/bin/zsh
# 55-hunt tier 2: all 526 floor-27 DB classes.
# Per class: extract bits -> emit every sides<=27 rep -> exact Z-rescore
# -> log best -> keep candidate dir only on a <=56 hit.
set -u
cd /Users/greg/projects/logic
R=matmul/found55/f27run
mkdir -p $R
python3 - <<'EOF'
names = set(open("matmul/found55/f27names.txt").read().split())
import os
os.makedirs("matmul/found55/f27run/bits", exist_ok=True)
n = 0
for line in open("matmul/dbcache/all_bits.txt"):
    name, b = line.split()
    if name in names:
        open(f"matmul/found55/f27run/bits/{name}.bits", "w").write(b + "\n")
        n += 1
print(f"extracted {n} class bits")
EOF
total=0
for f in $R/bits/*.bits; do
  name=$(basename $f .bits)
  total=$((total+1))
  cdir=$R/cands
  rm -rf $cdir && mkdir -p $cdir
  ./target/release/floors $f --emit-sides 27 --emit-cands $cdir \
      --threads 10 > /dev/null 2>&1
  n=$(ls $cdir | wc -l | tr -d ' ')
  if [ "$n" = "0" ]; then
    echo "$name: 0 slim reps (floor-27 unreachable at budget 27?)"
    continue
  fi
  out=$(./target/release/zrescore $cdir/*.bits --models 8 \
        --crestarts 300 --threads 10 --quiet 2>&1)
  best=$(echo "$out" | grep -o "best [0-9]*" | awk '{print $2}')
  echo "$name: $n reps, best $best"
  if echo "$out" | grep -q JACKPOT; then
    echo "$out" | grep JACKPOT
    mv $cdir $R/JACKPOT_$name
  elif [ "${best:-99}" -le 56 ]; then
    mv $cdir $R/HIT56_$name
  fi
done
echo "F27-CAMPAIGN-DONE ($total classes)"
