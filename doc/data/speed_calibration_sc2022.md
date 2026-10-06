# This Mac against the SAT Competition 2022 machines

Measured 2026-10-06 with `tools/gbd/speed_calibration.py`. A duo-run job here
runs about **3.0 times faster** than the same solver ran on the machines of
SC2022's anniversary track.

## Why it matters

The anniversary duo run compares satsuma and hydra_circuit_satsuma with the
28 sequential solvers of the SC2022 anniversary track on the same instances.
Their times are CPU seconds on StarExec, Intel Xeon E5-2609 at 2.4 GHz from
2012, and ours are wall seconds on an Apple M4 Pro running 10 jobs at once.
Counts under the same 5,000 s limit are only comparable after correcting for
the speed difference. Scaling our times by a factor k, on the first 1,248
instances both finished:

| beats the 2022 winner Kissat_MAB_ESA while k is below | by solved count | by PAR-2 |
|---|---|---|
| satsuma | 5.1 | 5.25 |
| hydra_circuit_satsuma | 5.7 | 5.7 |

Against the 2022 virtual best, the fastest of the 28 solvers on each
instance, the break-even is only 1.4 to 1.7.

## Method

The reference solver is kissat-sc2022-bulky, the 2022 track's most-solved
solver, whose source is kissat's `sc2022-bulky` tag. It was built with gcc in
the satsuma Docker image in the competition configuration, with FMA
contraction off. kissat's search does not depend on time, so it takes the same
steps here as in 2022 and the ratio of times is the hardware's.

It ran inside the same Docker VM as the duo run's satsuma jobs, in a slot
freed by lowering the duo run to 9 cores, so the machine carried the same 10
single-threaded jobs. The sample has 20 instances, one per family, which the
reference solved in 30 to 1,000 s, stratified by time with a fixed seed. Data:
`sat_benchmarks/runs/speed_calibration_sc2022/`.

## Result

All 20 verdicts matched. Official time over time here: median 2.99,
geometric mean 2.89, quartiles 2.79 to 3.12, range 1.82 to 3.83. CPU time
equalled wall time here, so load did not steal time from the measured job.

| instance | family | status | 2022 StarExec CPU s | here, wall s | ratio |
|---|---|---|---|---|---|
| velev-fvp-sat-3.0-b18 | hardware-verification | SAT | 30.9 | 9.9 | 3.12 |
| simon-mixed-s02bis-05 | misc-satex | SAT | 31.8 | 10.6 | 2.99 |
| instance_n9_i9_pp_ci_ce | parity-games | SAT | 31.9 | 11.4 | 2.79 |
| rpoc_xits_07_UNSAT | bioinformatics | UNSAT | 34.6 | 10.0 | 3.47 |
| uts-l06-ipc5-h35-unknown | planning | SAT | 43.5 | 11.3 | 3.83 |
| dalumul.miter.shuffled-as.sat03-349 | miter | UNSAT | 56.5 | 17.9 | 3.16 |
| UTI-15-10p1 | diagnosis | SAT | 81.1 | 28.7 | 2.83 |
| CNP-5-400 | coloring | SAT | 108.3 | 35.8 | 3.03 |
| AProVE07-08 | termination-analysis | UNSAT | 109.5 | 36.0 | 3.04 |
| sha1r17m66a_p | cryptography | SAT | 167.3 | 58.1 | 2.88 |
| jkkk-random-132906006204477-10-10-32-OR-unsat | ensemble-computation | UNSAT | 193.2 | 58.8 | 3.29 |
| sv-comp19_prop-reachsafety.square_5_true-unreach-call | software-verification | UNSAT | 218.4 | 87.0 | 2.51 |
| at-least-two-traffic_kkb_unknown | at-least-two-sol | UNSAT | 242.8 | 101.2 | 2.40 |
| Karatsuba7654321x1234567 | karatsuba-multiplication | SAT | 289.5 | 105.2 | 2.75 |
| em_7_3_6_cmp | edge-matching | SAT | 372.5 | 127.4 | 2.92 |
| Ptn-7824-b18 | pythagorean-triples | SAT | 400.2 | 128.8 | 3.11 |
| bvsub_08985.smt2 | bitvector | UNSAT | 427.1 | 235.1 | 1.82 |
| LABS_n079_goal006 | auto-correlation | SAT | 590.4 | 301.8 | 1.96 |
| mp1-klieber2017s-1600-024-eq | crafted-cec | UNSAT | 615.5 | 206.1 | 2.99 |
| mp1-blockpuzzle_7x10_s9_free6 | puzzle | UNSAT | 640.5 | 171.6 | 3.73 |

## Consequence for the duo run

At k = 3, on the first 1,248 instances, satsuma solves 975 with PAR-2 2,485
and hydra_circuit_satsuma 979 with 2,454, against the 2022 winner's 940 and
2,805. Even the largest ratio measured, 3.83, stays below the break-even, so
both beat the 2022 winner on these instances. Neither matches the 2022
virtual best's 1,010 and 2,120 once corrected.

Limits: the ratio varies by instance, and satsuma's kissat and symmetry
step may scale differently from 2022's kissat. The run has checks off, so it
compares answers, not checked certificates. The duo run has covered 23% of
the set so far.
