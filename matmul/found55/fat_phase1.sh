#!/bin/zsh
# Fat-sides 55 hunt, phase 1: the six interesting classes.
# Band: sides 28-29 where slim exhaust covered <=27 (sun + the three
# floor-26 classes); sides 29 where it covered <=28 (cn119, cn122).
set -u
cd /Users/greg/projects/logic
R=matmul/found55/fat
mkdir -p $R
hunt() { # hunt <name> <bits> <band-glob>
  local name=$1 bits=$2 glob=$3
  local cdir=$R/cands_$name
  rm -rf $cdir && mkdir -p $cdir
  echo "== $name: emit sides<=29 =="
  ./target/release/floors $bits --emit-sides 29 --emit-cands $cdir \
      --threads 10 2>&1 | tail -1
  local nfat=$(find $cdir -name "*-${glob}-*.bits" | wc -l | tr -d ' ')
  local nall=$(ls $cdir | wc -l | tr -d ' ')
  echo "$name: $nall emitted, $nfat in fat band ($glob)"
  if [ "$nfat" = "0" ]; then rm -rf $cdir; return; fi
  echo "== $name: zrescore fat band =="
  find $cdir -name "*-${glob}-*.bits" | \
    xargs ./target/release/zrescore --models 8 --crestarts 400 \
        --threads 10 --quiet 2>&1 | tee $R/$name.out
  if grep -q JACKPOT $R/$name.out; then
    echo "*** KEEPING $cdir (jackpot) ***"
  else
    rm -rf $cdir
  fi
}
hunt sun56    matmul/perminov_cache/bits/sun56.bits      's2[89]'
hunt cn122    matmul/perminov_cache/bits/cr58-cn122.bits 's29'
hunt cn119    matmul/perminov_cache/bits/cr58-cn119.bits 's29'
hunt i46w205  matmul/found55/f26/i46w205c23ci-017.bits   's2[89]'
hunt i46w221  matmul/found55/f26/i46w221c23ci-009.bits   's2[89]'
hunt i73w191  matmul/found55/f26/i73w191c236f-000.bits   's2[89]'
echo PHASE1-DONE
touch $R/phase1.done
