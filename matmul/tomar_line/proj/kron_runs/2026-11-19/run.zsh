#!/bin/zsh
cd ${0:A:h}/../..
D=kron_runs/2026-11-19; S=../../perminov_cache/f70078c; B='13x14x14=1564,15x16x16=2202'
I14=$(python3 -c "print(';'.join(f'I{i}' for i in range(14)))"); I16=$(python3 -c "print(';'.join(f'I{i}' for i in range(16)))")
python3 kron_proj_multi.py $S/14x14x14_m1593_Q.json $D/status_f70078c.json $D/b14_1593_singles.csv "$I14" --workers 4 --paths $D/paths --bar $B > $D/b14_1593_singles.log 2>&1 &
python3 kron_proj_multi.py $S/16x16x16_m2236_Q.json $D/status_f70078c.json $D/b16_2236_singles.csv "$I16" --workers 6 --paths $D/paths --bar $B > $D/b16_2236_singles.log 2>&1 &
wait; echo ALL DONE $(date) >> $D/run.done
