#!/bin/bash
for i in $(seq 1 240); do grep -q '^# done' /private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/run_perfect.log && [ -s /private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/pcl/classes.json ] && break; sleep 30; done
echo "# P side start $(date '+%H:%M')"
cd /Users/greg/projects/logic/matmul/dps48/rfc2610; timeout 1500 /usr/bin/python3 -I pside.py /private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/pcl 60 2 2>&1 | cut -c1-120
echo "# done $(date '+%H:%M')"
