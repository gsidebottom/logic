#!/bin/bash
# Coordinate descent on the model with every side held to its operation budget.
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
SL=/Users/greg/projects/logic/target/release/slpopt; DD=$SP/plinopt_main/data
W=$1; R0=$2; BR=$3; mkdir -p $W; p=$W/cur
for s in L R P; do cp $DD/4x4x4_48_accurate_262_$s.sms ${p}_$s.sms; done
cp $DD/4x4x4_48_accurate_262_L.slp ${p}_L.slp; cp $DD/4x4x4_48_accurate_262_P.slp ${p}_P.slp; cp $R0 ${p}_R.slp
for round in 1 2 3; do
  for m in P L R; do
    case $m in L) b=72;; R) b=$BR;; P) b=112;; esac
    $SL search --scheme $p --matrix $m --init ${p}_$m.slp --out $W/new_$m.slp --steps ${4:-20000} --restarts 4 --threads 4 --seed $round --maxops $b 2>&1 | grep -E "^# best" | sed "s/^/round $round $m: /" | cut -c1-80
    cp $W/new_$m.slp ${p}_$m.slp
  done
done
$SL model start $DD/4x4x4_48_accurate_262 polished $p 2>&1 | cut -c1-110
