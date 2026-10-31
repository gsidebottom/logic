#!/bin/bash
# lns48 on every line-fixed V at the record P (vlines.py), P fixed at 89.  A 200 needs L + R <= 111.
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad; D=/Users/greg/projects/logic/matmul/dps48; W=$SP/td
cd $D
echo "# V-lines sweep start $(date '+%Y-%m-%d %H:%M')"
LNS_NAIVE=1 FIXED_P=89 PLINOPT_BIN=$SP/plinopt_main/bin R48_SCRATCH=$SP /usr/bin/env timeout 2700 /usr/bin/python3 patel/sweep.py --out $W/sweep_vl --pool $W/vl/pool.csv --procs 12 --a-seconds 30 --b-seconds 120 --c-seconds 300 --a-keep 16 --b-keep 4 2>&1 | grep -v "^$" | cut -c1-200
echo "sweep exit ${PIPESTATUS[0]}"
echo "# done $(date '+%H:%M')"
