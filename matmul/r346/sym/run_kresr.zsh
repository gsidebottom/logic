#!/bin/zsh
# kresr campaign (2026-11-15): the k-subset re-solve in characteristic 0.  The two <3x3x6:40> schemes by full enumeration
# (their F2 images are degenerate), then the <3x4x6:54> at k = 8 from kres8's candidate list (k = 5..7: kresr_54_k5-7.log).
cd /Users/greg/projects/logic
R=matmul/r346/results; S=matmul/r346/schemes
timeout 3000 target/release/kresr $S/3x3x6_m40_dps.json --all 6-8 --out $R/kresr_red > $R/kresr_40dps.log 2>&1
timeout 3000 target/release/kresr $S/3x3x6_m40_orig.json --all 3-8 --out $R/kresr_red > $R/kresr_40orig.log 2>&1
timeout 7200 target/release/kresr $S/3x4x6_m54_perminov_ZT.json /private/tmp/claude-501/-Users-greg-projects-logic/3d45768d-4e94-4613-987d-3cadfd01d9af/scratchpad/kresr/l54_k8.txt --out $R/kresr_red > $R/kresr_54_k8.log 2>&1
echo done > $R/kresr_campaign.done
