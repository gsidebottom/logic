#!/bin/bash
# LNS program search (lns48, the Rust port of Patel's method) on Alexandre's 203-point L and R
# (48x16, entries 0, +-1, +-1/2): first 12 naive seeds x 180 s per matrix, as the record run on our
# 201 point (L 55 in 11/12, R 57 in 12/12), then 12 seeds x 180 s started from his 57-operation
# programs.  Costs in PLinOpt's model: one operation per produced signal, additions and scalings.
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
LNS=/Users/greg/projects/logic/target/release/lns48
F=$SP/rfc2610/files
cd $SP/rfc2610/lns
echo "# lns48 on 4x4x4_48_203 L and R, $(date '+%Y-%m-%d %H:%M')"
for m in L R; do
  echo "## $m, naive seeds, 12 x 180 s  $(date '+%H:%M')"
  mkdir -p naive_$m; $LNS --sms $F/4x4x4_48_203_$m.sms --out naive_$m --wall 180 --seeds 12 --log 60 > naive_$m.log 2>&1; echo "exit $?"; grep -i "best\|cost" naive_$m.log | tail -3
done
for m in L R; do
  echo "## $m, seeded from Alexandre's 57-operation program, 12 x 180 s  $(date '+%H:%M')"
  mkdir -p seeded_$m; $LNS --slp $F/4x4x4_48_203_$m.slp --sms $F/4x4x4_48_203_$m.sms --out seeded_$m --wall 180 --seeds 12 --log 60 > seeded_$m.log 2>&1; echo "exit $?"; grep -i "best\|cost" seeded_$m.log | tail -3
done
echo "## emitted programs:"; ls -la naive_L naive_R seeded_L seeded_R | head -40
echo "# done $(date '+%H:%M')"
