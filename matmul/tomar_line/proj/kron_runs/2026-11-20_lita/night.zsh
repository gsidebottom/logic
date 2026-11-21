#!/bin/zsh
# night.zsh: hands the single-deletion results of the larger squares to the rounds as they arrive.
#   lane M: 23^3 .. 26^3, rounds 2-5, started when the 26^3 singles are done;
#   lane B: 27^3 .. 32^3, rounds 2-3, started when all singles are done.
# (lane A, 17^3 .. 22^3, rounds 2-9, was started by hand.)  Every wait is bounded (14 h).
D=${0:A:h}; cd $D
wait_for() { local n=0; while ! grep -q "$1" progress; do sleep 30; n=$((n+1)); (( n > 1680 )) && { echo "night: gave up waiting for $1" >> progress; exit 1 }; done }
wait_for 'singles 26 exit'
./verify.zsh kron_runs/2026-11-20_lita/paths/23 kron_runs/2026-11-20_lita/paths/24 kron_runs/2026-11-20_lita/paths/25 kron_runs/2026-11-20_lita/paths/26 > logs/verify_23_26.out 2>&1
python3 -I seed.py M 2 23 26 > logs/seed_M.out 2>&1
RMAX=5 nohup ./rounds2.zsh M 2 > logs/rounds_M.out 2>&1 &
wait_for 'singles ALL DONE'
./verify.zsh kron_runs/2026-11-20_lita/paths/27 kron_runs/2026-11-20_lita/paths/28 kron_runs/2026-11-20_lita/paths/29 kron_runs/2026-11-20_lita/paths/30 kron_runs/2026-11-20_lita/paths/31 kron_runs/2026-11-20_lita/paths/32 > logs/verify_27_32.out 2>&1
python3 -I seed.py B 2 27 32 > logs/seed_B.out 2>&1
RMAX=3 nohup ./rounds2.zsh B 2 > logs/rounds_B.out 2>&1 &
echo "night: all lanes started $(date)" >> progress
