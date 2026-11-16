#!/bin/bash
# After -ffp-contract=off (2026-11-16): the exact errors of the plans with an R336 level that the report quotes,
# against the campaign's (contracted) values; the same inputs and exact references as the campaign.
# results/r336_nocontract_2026-11-16.txt
cd "$(dirname "$0")" || exit 1
export FMM_CALIB_DIR="$PWD/results" FMM_EXACT=1 FMM_REFCACHE=/private/tmp/claude-501/-Users-greg-projects-logic/3d45768d-4e94-4613-987d-3cadfd01d9af/scratchpad/refcache
echo "# R336 plans without FMA contraction; $(date '+%Y-%m-%d %H:%M'); campaign err64: 13824 f32 R336+4/R363/G6 3.34e-6, R363+4/R336/G6 3.33e-6, R336/G 3.80e-6; 6912 f32 R336/G 2.27e-6; 13824 f64 R363+3/R336/G3 6.40e-15, R336+3/R363/G3 6.72e-15, R336/G 7.21e-15; 6912 f64 R336+2/R363/G6 3.66e-15, R336/G 4.53e-15"
./build/bench_fmm -n 13824 -t f -r 1 -m plan=R336+4/R363/G6,plan=R363+4/R336/G6,plan=R336/G | grep -E "^plan=" | grep -oE "^plan=[^ ]+|err64 [0-9.e+-]+"
./build/bench_fmm -n 6912 -t f -r 1 -m plan=R336/G | grep -E "^plan=" | grep -oE "^plan=[^ ]+|err64 [0-9.e+-]+"
./build/bench_fmm -n 13824 -t d -r 1 -m plan=R363+3/R336/G3,plan=R336+3/R363/G3,plan=R336/G | grep -E "^plan=" | grep -oE "^plan=[^ ]+|err64 [0-9.e+-]+"
./build/bench_fmm -n 6912 -t d -r 1 -m plan=R336+2/R363/G6,plan=R336/G | grep -E "^plan=" | grep -oE "^plan=[^ ]+|err64 [0-9.e+-]+"
echo "# done $(date '+%H:%M')"
