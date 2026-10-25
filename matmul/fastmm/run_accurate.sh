#!/bin/bash
# after switching D48 to the accurate DPS program: recalibrate (the cache is keyed by the
# kernels), validate the error model and the planner (run_accuracy.sh), and test the library
cd "$(dirname "$0")" || exit 1
echo "# recalibration with the accurate D48 kernels $(date '+%Y-%m-%d %H:%M')"
for t in f d; do ./build/bench_fmm -n 16384 -t $t -p | grep -v '^#   '; done
echo "# calibration done $(date '+%H:%M')"
./run_accuracy.sh > results/accuracy_accurate_2026-10-25.txt 2>&1
echo "# accuracy done $(date '+%H:%M')"
FMM_CALIB_DIR=results ./build/test_fmm > results/test_fmm_accurate_2026-10-25.txt 2>&1
echo "# test done $(date '+%H:%M')"
