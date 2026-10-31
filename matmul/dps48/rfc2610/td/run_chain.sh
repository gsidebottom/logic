#!/bin/bash
for i in $(seq 1 150); do grep -q '^# done' /private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/run_td.log && break; sleep 30; done
/Users/greg/projects/logic/matmul/dps48/rfc2610/run_vl.sh > /private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/run_vl.log 2>&1
/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/run_perfect.sh > /private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/run_perfect.log 2>&1
/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/run_pside.sh > /private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/run_pside.log 2>&1
