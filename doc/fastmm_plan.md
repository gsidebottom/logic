# Practical fast matrix multiplication: plan

Started 2026-10-24.  Code and results: `matmul/fastmm/` (build with `make`; sweeps
`run_bench.sh`, `run_blocked.sh`, `run_hybrid.sh`, `run_auto.sh`, `run_probes.sh`,
`run_streams.sh`, `run_auto_streams.sh`, `run_neon.sh`, `run_neon2.sh`, `run_pipe.sh`,
`run_auto_pipe.sh`, `run_pipe2.sh`, `run_accuracy.sh`, `run_pad.sh`; results in
`matmul/fastmm/results/`).
`bench_fmm -m auto` picks the plan per size and precision from a calibrated cost model
(`auto:g`: the fastest plan whose error grows at most g-fold over the classical GEMM's);
`bench_fmm -n N -p` prints the planner's choices.  The library: `fmm.h` (`fmm_sgemm`,
`fmm_dgemm`, `fmm_calibrate`, `fmm_plan`, `fmm_release`), `build/libfmm.a`.

## Goal

Matrix multiplication that runs faster on real machines.  The time is set by two things,
not by arithmetic operation counts:

- the base-case products, done by a tuned GEMM (here Apple Accelerate, which runs on the
  M4 Pro's SME matrix units at about 3 TFLOP/s in f32 and 0.8 TFLOP/s in f64), and the size
  at which that GEMM is most efficient;
- data movement through the memory hierarchy: how many times the blocks of A, B, C and the
  temporaries travel between main memory, caches and registers.

## Where we stand (2026-10-24, Apple M4 Pro, 64 GB)

Speedup over the best classical variant (one GEMM, or classical done as blocked GEMMs of
n/2, n/4 or n/8 -- Accelerate is sometimes faster on blocks than on one big call), median of
5 interleaved rounds, `results/blocked_2026-10-24.txt`:

| n | precision | Strassen 1 level | 2 levels | 3 levels | Strassen^2 fused | ours fused |
|---|---|---|---|---|---|---|
| 8192 | f32 | 1.16 | 1.24 | 1.04 | 1.30 | **1.34** |
| 8192 | f64 | 1.04 | 1.17 | 1.21 | 1.20 | **1.23** |
| 16384 | f32 | 1.01 | 1.14 | **1.22** | 1.15 | 1.16 |
| 16384 | f64 | 1.13 | 1.24 | **1.38** | 1.25 | 1.28 |

"Fused" means one level done as three streaming passes (L on A, R on B, P on the products):
each pass reads every input block once and writes every output block once, with the
scheme's linear program evaluated per element position in registers.  Recursive Strassen
uses the same fused 2x2 passes at every level.  The big classical f32 GEMM at 16384 is
noisy (2.6-3.1 s across runs), so treat that row as +-10%.

What the numbers say:

1. Fast schemes pay at scale: 16-38% over the best classical variant at n = 8192-16384.
   Below 4096 they lose (block GEMMs are less efficient and the passes do not amortize).
2. Memory passes decide between schemes, not operation counts.  A fused 4x4 level moves
   16 + 48 blocks per side, half the bytes of two Strassen levels; measured 35-40% less pass
   time than two recursive levels.  Our 201 operations against Strassen^2's 165 made no
   measurable difference once fused.
3. Our 48-scheme beats Strassen^2 (fused, 49 products) by 1-3%: the one GEMM it saves.
4. At 16384 three Strassen levels win: 343 products of 2048 save the most multiplication,
   but their passes cost 3x ours.
5. Run one block operation at a time (as most libraries do), our scheme's 201 passes cost
   about 2.5x the fused passes.

Hybrids (`results/hybrid_2026-10-24.txt`, same protocol): the best method at every tested
size and precision uses our 48-scheme.

| n | precision | best method | speedup | runner-up |
|---|---|---|---|---|
| 8192 | f32 | ours, one fused level (48 GEMMs of n/4) | 1.20 | Strassen^2 fused 1.16 |
| 8192 | f64 | ours + one Strassen level below (336 GEMMs of n/8) | 1.28 | ours alone 1.26 |
| 16384 | f32 | ours + one Strassen level below | 1.375 | Strassen^2 + Strassen 1.36, three Strassen levels 1.31 |
| 16384 | f64 | ours, two fused levels (2,304 GEMMs of n/16) | 1.54 | ours + Strassen 1.41, four Strassen levels 1.39 |

The cost model's predictions held: ours + Strassen at 16384 was predicted at 2.06 s (f32)
and 7.51 s (f64), measured 2.062 s and 7.59 s, beating three Strassen levels by 4.9% and 4.3%.
Two levels of ours were predicted slower (1024-sized GEMMs) and were the fastest method in
f64: their passes cost 0.81 s against 1.35 s for four Strassen levels, with 2,304 products
against 2,401.  Error stays at rounding level and grows with depth (f64: 2.2e-14 one level of
ours, 6.3e-14 ours + Strassen, 1.0e-13 two levels of ours vs 1.1e-13 four Strassen levels).

Fused multiply-add (`results/fma_2026-10-24.txt`): no gain on this machine.  The program's 4
halvings each feed 4-5 additions, so `-ffp-contract=fast` fuses nothing; folding every use into
`fma(x, 0.5, y)` turns 4 multiplies into 18 FMLAs but adds 7 negations (NEON has no vector form
of x*s - y), and the passes are bandwidth-bound: identical pass times, identical results (halving
is exact).  FMA would matter for points with many single-use scalings, under a cost model where
scalings fused into additions are free, and once the passes become compute-bound.

Automatic plan choice (`results/auto_2026-10-24.txt`).  A plan is a sequence of fused levels
from the top -- SW (Strassen-Winograd), D48 (ours) -- ending in a GEMM (G), or classical
blocked 2x2 (B2) on its own.  `auto` runs the plan with the smallest predicted time:
cost(n) = min(leaf, passes of a level at n/g + r * cost(n/g)), a dynamic program over the first
level, each leaf GEMM priced by the level it sits in.  The calibration is measured once per
machine and precision (about 75 s for n up to 16384; cached in `results/calib_f32.txt`,
`calib_f64.txt` with the machine, padding and format, remeasured when any differs): one GEMM and
one blocked call at each size, alone, with cold caches; and for each level type and block size,
its three passes and its GEMM time per product, measured together by running the level.

| n | precision | auto's plan | predicted (s) | measured (s) | best classical variant (s) | speedup |
|---|---|---|---|---|---|---|
| 2048 | f32 | G | 0.0052 | 0.0053 | 0.0052 (G) | 1.00 |
| 4096 | f32 | SW/G | 0.041 | 0.045 | 0.048 (G) | 1.06 |
| 8192 | f32 | D48/G | 0.277 | 0.275 | 0.330 (G) | 1.20 |
| 16384 | f32 | SW/D48/G | 2.004 | 1.998 | 2.874 (B2) | 1.44 |
| 2048 | f64 | SW/G | 0.020 | 0.021 | 0.022 (G) | 1.03 |
| 4096 | f64 | D48/G | 0.143 | 0.141 | 0.165 (G) | 1.17 |
| 8192 | f64 | SW/D48/G | 1.033 | 1.007 | 1.380 (G) | 1.37 |
| 16384 | f64 | D48/D48/G | 7.098 | 6.942 | 10.832 (B2) | 1.56 |

At every point auto's plan was the fastest method measured (against the named methods and the
planner's runners-up, medians of 5-9 interleaved rounds; where auto's plan was also run under
its own name, the two medians differ by 0.4-1.4%).  Predictions for the fast plans at
8192-16384 are within 0.3-3%; the 4096 f32 run was slow throughout (classical 13% over its
calibration).  What the planner found:

1. Level order matters.  Strassen on top of ours (SW/D48/G) beats ours on top of Strassen
   (D48/SW/G, our best hand-made hybrid) with the same 336 products: its passes move 9.75 n^2
   elements per side against 12.25 n^2, because the larger expansion (ours writes 3x the data it
   reads, Strassen 1.75x) belongs at the smaller level.  It is the new best at 16384 f32 (1.99 s
   against 2.06 s) and 8192 f64 (1.01 s against 1.05 s).
2. f64 rewards depth and f32 does not: the f64 GEMM keeps its rate down to 1024 (0.81 TFLOP/s
   against 0.82-0.85 at 2048-8192), the f32 GEMM drops below 2048 (3.0 TFLOP/s at 1024, 2.6 at
   512, against 3.2-3.3).  Two levels of ours win only at 16384 f64.
3. A GEMM shorter than about 1 ms takes 13-27% longer called back to back, as inside a plan,
   than called alone (f32 at 512-1024, f64 at 256-512; `bench_fmm -G` times it three ways).  The
   first calibration timed single calls and picked two levels of ours at 8192 f64 (1.144 s)
   where SW/D48/G runs in 1.017 s (`results/auto_2026-10-24_calib1.txt`); pricing each level's
   GEMMs inside the level fixed every miss.

How much of the machine the GEMMs use (`probe_threads.c`, `results/probes_2026-10-24.txt`).
The M4 Pro has one SME matrix unit per cluster (two performance clusters of 5 cores, one
efficiency cluster of 4), shared by the cluster's cores.  Accelerate drives each performance
cluster's unit from one thread, so its GEMM keeps 2-3 cores busy and leaves the rest idle:

| n = 2048 | f32 GFLOP/s | f64 GFLOP/s |
|---|---|---|
| Accelerate's GEMM (as bench_fmm calls it) | 3,295 | 800 |
| one single-threaded GEMM stream | 1,652 | 380 |
| two streams | 3,343 | 782 |
| three streams | 3,631 | 863 |
| NEON fused multiply-add peak, 10 performance cores, registers only | 1,077 | 540 |
| two GEMM streams + 8 NEON threads (GEMM + NEON) | 3,225 + 837 = 4,062 | 725 + 394 = 1,119 |
| Accelerate's GEMM + 12 NEON threads | 1,326 + 1,083 | 566 + 482 |

The GEMMs are bound by the SME units: one stream gets half of Accelerate's rate, two get all
of it.  Three single-threaded streams beat Accelerate's own threading by 10% (f32) and 8% (f64)
-- the efficiency cluster's unit, or better overlap of packing with SME work; not yet separated.
The vector units of the 8 cores left idle could add up to 25% (f32) and 50% (f64) at their
register-only peak.  Oversubscribing the cores collapses the GEMM rate.

GEMM streams (`results/streams_2026-10-24.txt`, `results/auto_streams_2026-10-24.txt`).  The
third stream's gain is not the efficiency cluster: its SME unit is slow (136 GFLOP/s f32, 42
f64 alone), and two performance streams plus one background-priority stream reach only 3,503
(f32) / 813 (f64), against 3,676 / 874 for three normal streams.  The third stream shares a
performance cluster's unit and keeps it busier (one thread leaves it idle while it packs
operands, and between calls).  In a plan, the leaf Gk runs a level's products as k
single-threaded GEMM streams taking products in turn.  Interleaved A/B against one product at a
time with Accelerate's own threading (medians, s):

| n | prec | plan (GEMM size) | G | G2 | G3 | G4 | G6 |
|---|---|---|---|---|---|---|---|
| 4096 | f32 | SW/G (2048) | 0.043 | 0.045 | 0.040 | 0.041 | 0.046 |
| 4096 | f32 | D48/G (1024) | 0.046 | 0.042 | 0.040 | 0.039 | 0.038 |
| 8192 | f32 | D48/G (2048) | 0.280 | 0.275 | 0.255 | 0.266 | 0.289 |
| 16384 | f32 | SW/D48/G (2048) | 2.007 | 2.025 | 1.859 | 1.929 | 2.070 |
| 4096 | f64 | D48/G (1024) | 0.142 | 0.142 | 0.131 | 0.149 | 0.190 |
| 8192 | f64 | SW/D48/G (1024) | 1.007 | 1.023 | 0.966 | 1.103 | 1.353 |
| 16384 | f64 | D48/D48/G (1024) | 7.064 | 7.268 | 6.613 | 7.374 | 8.919 |

Three streams win at most sizes, more streams win for the smallest GEMMs (f32 at 1024, f64 at
512 and below) and lose badly at larger ones (6 streams +26-34% in f64 at 1024).  The
calibration now times each level's products with 0, 3, 4 and 6 streams (about 3 minutes per
precision) and the planner chooses per plan.  Validation, same protocol as above (the best
classical variant from the same run):

| n | precision | auto's plan | predicted (s) | measured (s) | best classical (s) | speedup | best plan without streams (s) |
|---|---|---|---|---|---|---|---|
| 2048 | f32 | G | 0.0052 | 0.0054 | 0.0052 | 1.00 | -- |
| 4096 | f32 | D48/G6 | 0.036 | 0.036 | 0.042 | 1.17 | 0.042 (G) |
| 8192 | f32 | D48/G3 | 0.257 | 0.254 | 0.333 | 1.31 | 0.283 (D48/G) |
| 16384 | f32 | D48/D48/G6 | 1.861 | 1.838 | 2.688 | 1.46 | 1.995 (SW/D48/G) |
| 2048 | f64 | D48/G6 | 0.018 | 0.018 | 0.021 | 1.19 | 0.020 (SW/G) |
| 4096 | f64 | SW/D48/G6 | 0.132 | 0.133 | 0.166 | 1.25 | 0.141 (D48/G) |
| 8192 | f64 | D48/D48/G6 | 0.905 | 0.908 | 1.297 | 1.43 | 1.006 (SW/D48/G) |
| 16384 | f64 | SW/D48/D48/G6 | 6.470 | 6.499 | 11.129 | 1.71 | 6.987 (D48/D48/G) |

Auto's plan was the fastest measured or within 0.6% of it at every point (at 16384 f32
SW/D48/G3 ran 1.830 s, predicted 0.0008 s slower; at 4096 f64 D48/G3 ran 0.132 s), and
predictions are within 0.3-1.3% at 4096-16384.  Streams take 6-14% off the best plans and make
fast multiplication pay from n = 2048 in f64 and 4096 in f32.  Small GEMMs become cheap, so the
planner goes deeper; the price is accuracy: f64 error at 16384 is 2.0e-13 for SW/D48/D48 against
1.0e-13 for D48/D48, and f32 error 5.9e-5 for D48/D48 against 3.3e-5 for SW/D48 (the planner
does not price accuracy yet).

NEON products on the idle cores (negative result; `neon_gemm.h`, `neon_test.c`,
`results/neon_2026-10-24.txt`, `neon_products_2026-10-24.txt`, `neon_whole_2026-10-24.txt`).
The NEON GEMM (GotoBLAS packing, 8 x 8 f32 and 4 x 8 f64 micro-kernels of lane-indexed fused
multiply-adds) runs at 90-93% of one core's register peak (105-109 GFLOP/s f32, 54-55 f64) and
82-87% on 7 cores.  Beside three SME streams it slows the SME units, which share each cluster's
L2: the first loop order (all of A streamed from L2 for every 8-column panel of B) cost them
28-42%; blocking A in L1 cut that to 3-33%.  Steady state, three SME streams plus NEON threads
(GFLOP/s, total against SME alone):

| | + 2 NEON | + 4 NEON | + 7 NEON |
|---|---|---|---|
| f32, n = 1024 | +3% | +6% | +3% |
| f32, n = 2048 | +3% | +3% | 0% |
| f64, n = 1024 | +5% | +2% | 0% |
| f64, n = 2048 | +9% | +14% | +14% |

In plans (leaf GkNj: the level's last j products on 4 NEON threads while k streams take the
rest) the best share gained 1.3-2.7% at the median (8192 f32 D48/G3N2 0.251 s against 0.258;
16384 f64 SW/D48/D48/G6N4 6.390 against 6.477), a wrong share lost up to 40%, and single rounds
varied by 8-10% with core placement, which macOS does not let a program choose.  Not adopted:
NEON is a small part of the machine's matrix throughput (0.7 of 4.3 TFLOP/s f32, 0.33 of 1.2 f64)
and taking it costs the SME units most of what it adds.

Pipelined passes (`probe_overlap.c`, `results/overlap_probe_2026-10-24.txt`,
`results/pipe_2026-10-24.txt`).  A streaming pass beside the SME streams slows them even more
than a NEON GEMM does (GFLOP/s of the streams, pass GB/s):

| | streams alone | + 2 pass threads | + 4 | + 7 |
|---|---|---|---|---|
| f64, blocks 512, 6 streams | 1,003 | 858, 49 GB/s | 714, 79 | 613, 95 |
| f64, blocks 1024, 3 streams | 931 | 681, 49 | 383, 75 | 128, 92 |
| f32, blocks 2048, 3 streams | 3,613 | 3,092, 47 | 2,212, 70 | 617, 90 |

(the pass alone on all 10 cores: 115-122 GB/s).  Hidden behind the GEMMs on 2-4 threads a pass
still costs less than run alone on all cores: at f64 blocks 512 with 2 threads it slows the
streams by 14% while it runs at 49 GB/s, about 35% of its cost alone.  So a level whose products
are themselves levels over GEMM streams can pipeline them (written X+p, p pass threads): while
the streams compute sub-problem q, the pass threads write sub-problem q - 1's result and the
factors of sub-problem q + 1, the scratch below double-buffered.  Interleaved A/B (medians, s):

| n | prec | plan | level by level | +1 | +2 | +3 | +4 |
|---|---|---|---|---|---|---|---|
| 8192 | f32 | SW/D48/G3 | 0.285 | 0.339 | 0.268 | 0.263 | 0.267 |
| 16384 | f32 | D48/D48/G6 | 1.843 | 2.074 | 1.690 | 1.689 | 1.714 |
| 16384 | f32 | SW/D48/G3 | 1.828 | 1.970 | 1.796 | 1.777 | 1.792 |
| 4096 | f64 | SW/D48/G6 | 0.132 | 0.149 | 0.125 | 0.121 | 0.120 |
| 4096 | f64 | D48/D48/G6 | 0.154 | 0.202 | 0.135 | 0.128 | 0.120 |
| 8192 | f64 | D48/D48/G6 | 0.905 | 0.992 | 0.804 | 0.803 | 0.801 |
| 8192 | f64 | SW/D48/G3 | 0.958 | 1.068 | 0.978 | 0.960 | 0.963 |
| 16384 | f64 | SW/D48/D48/G6 (middle level) | 6.444 | 6.999 | 5.769 | 5.758 | 5.726 |

Pipelining takes 8-22% off the plans over 6-stream leaves; one pass thread is too few (the
passes become the critical path) and plans over 3 streams of 1024-blocks in f64 gain nothing
(those streams are the most sensitive to pass traffic, see the probe).  The calibration times a
pipeline of 2 and of 10 synthetic sub-problems per level type, block size, stream count (3, 6)
and pass threads (2, 3, 4): the slope is the steady time per sub-problem, the rest the fill and
drain (2 and 4 sub-problems left a few percent of noise in the slope, which a level of 48
multiplies: one wrong pick at 16384 f32); sub-problems under 1 ms are not pipelined (per-step
dispatch and noisy calibration: one wrong pick at 2048 f64).  Validation
(`results/auto_pipe_2026-10-24.txt`, best classical variant from the same run):

| n | precision | auto's plan | predicted (s) | measured (s) | best classical (s) | speedup | fastest measured |
|---|---|---|---|---|---|---|---|
| 2048 | f32 | G | 0.0052 | 0.0053 | 0.0053 | 1.00 | auto |
| 4096 | f32 | D48/G6 | 0.036 | 0.039 | 0.049 | 1.26 | SW+4/D48/G6 0.037 |
| 8192 | f32 | D48+4/D48/G6 | 0.233 | 0.237 | 0.336 | 1.42 | auto |
| 16384 | f32 | D48+3/D48/G6 | 1.685 | 1.666 | 2.685 | 1.61 | auto |
| 2048 | f64 | D48/G6 | 0.018 | 0.018 | 0.021 | 1.18 | auto |
| 4096 | f64 | D48+4/D48/G6 | 0.120 | 0.121 | 0.164 | 1.36 | auto (tie) |
| 8192 | f64 | D48+3/D48/G6 | 0.799 | 0.805 | 1.370 | 1.70 | D48+4/D48/G6 0.799 |
| 16384 | f64 | SW/D48+3/D48/G6 | 5.721 | 5.751 | 11.204 | 1.95 | SW/D48+4/D48/G6 5.712 |

Predictions are within 0.5-1.8% at 8192-16384.  Auto's plan is the fastest measured or within
0.75% everywhere but 4096 f32, a run 15% slow throughout, where it was 5% behind a plan predicted
0.8% slower; with only 2 and 4 pass threads calibrated the 16384 f32 pick was D48+4/D48/G6 (1.682 s
here), with 3 it is the fastest plan measured.  The classical variants drift between runs (16384
f64: 10.7-11.5 s), so read the speedups as +-5%.  Against the start of the day (one fused level
of ours, 1.34x at 8192 f32 and 1.28x at 16384 f64 over the best classical variant) the
whole-machine plans reach 1.42x and 1.95-2.01x (`results/auto_pipe_2026-10-24_p24.txt`: 2.01x).

The top levels' passes (`results/pipe2_2026-10-24.txt`).  Pipelining hides only the passes of
the level just above the GEMMs; the rest stays sequential: 6-12% of auto's two-level plans
(the top level's first L/R pass and last P pass) and 8% of SW/D48+3/D48/G6 at 16384 f64 (the top
SW passes and the seven middle D48 levels' own passes).  In a two-level plan nothing runs beside
the top passes: the first sub-problem needs all of S and T, and the P pass needs every product,
so hiding them means splitting each pass into output groups that re-read their inputs (estimated
1-2% net; not built).  In a three-level plan the middle level's passes can run in the
background of the neighbouring middle sub-problems' pipelines (written X+/Z+p/Y/Gk: the pass
threads take chunks of sub-problem i - 1's P pass and i + 1's L and R passes when their own are
done and GEMMs still run; the middle scratch double-buffered):

| n | prec | plan | one-level pipeline | two-level |
|---|---|---|---|---|
| 16384 | f64 | SW/D48+4/D48/G6 | 5.727 | 5.594 (-2.3%) |
| 16384 | f64 | SW/D48+3/D48/G6 | 5.742 | 5.649 (-1.6%) |
| 16384 | f64 | D48/D48+4/D48/G6 | 6.007 | 5.936 (-1.2%) |
| 16384 | f32 | SW/D48+4/D48/G6 | 1.711 | 1.713 |
| 16384 | f32 | SW/D48+3/D48/G6 | 1.886 | 1.928 (+2.2%) |
| 8192 | f64 | SW/D48+3/D48/G6 | 0.934 | 0.957 (+2.5%) |

A 2% gain at the one point where a three-level plan wins (SW+/D48+4/D48/G6 at 16384 f64, 5.594
s, the fastest plan measured there); where the pipeline below has little idle pass time the
background passes only add interference.  Not in the planner (it would need two-level pipelines
calibrated, about a minute per precision, for 2% at one size); the plan syntax runs it.

Accuracy budget (`results/accuracy_2026-10-25.txt`).  Fast schemes trade accuracy for speed,
and the deeper plans auto picks double or triple the error of a one-level plan.  A plan's error
(max-norm, relative, against the classical GEMM on uniform random inputs) is well described by
the classical error scale times one factor per fused level, growing like sqrt(n) with the size:
the calibration measures SW/G, D48/G and D48/D48/G at n = 2048 and fits the factors (SW 2.49,
D48 3.39 in f32; 2.51, 3.44 in f64; the order of the levels immaterial, streams and pipelines
leave the arithmetic unchanged).  Predicted against measured, 16384:

| plan | f32 measured | f32 predicted | f64 measured | f64 predicted |
|---|---|---|---|---|
| SW/G | 1.28e-5 | 1.13e-5 | 2.27e-14 | 1.92e-14 |
| D48/G | 1.64e-5 | 1.53e-5 | 3.21e-14 | 2.64e-14 |
| SW/SW/G | 1.85e-5 | 2.80e-5 | 3.82e-14 | 4.83e-14 |
| SW/D48/G | 3.29e-5 | 3.81e-5 | 5.53e-14 | 6.63e-14 |
| D48/D48/G | 5.86e-5 | 5.18e-5 | 1.02e-13 | 9.10e-14 |
| SW/D48/D48/G | 1.08e-4 | 1.29e-4 | 1.98e-13 | 2.28e-13 |

Within 25% across 4096-16384 except two Strassen levels (over-predicted by up to 50%, the safe
side).  In f32 the same errors against an f64 product of the inputs agree with these to 2%, and
the classical f32 GEMM's own error is 1.3-1.6x the model's classical scale (3.0e-6, 4.6e-6,
7.2e-6 at 4096, 8192, 16384), so a growth g is about g / 1.5 times the classical GEMM's actual
error.  `auto:g` (or `FMM_MAX_GROWTH=g`) takes the fastest plan with growth at most g:

| n | prec | auto | auto:16 | auto:8 | auto:2 |
|---|---|---|---|---|---|
| 16384 | f32 | D48+3/D48/G6, 1.79 s, 5.9e-5 | same | D48/G3, 2.16 s, 1.6e-5 | B2, 3.14 s |
| 16384 | f64 | SW/D48+3/D48/G6, 5.79 s, 2.0e-13 | D48/D48/G3, 6.50 s, 1.0e-13 | D48/G3, 7.73 s, 3.2e-14 | B2, 10.68 s |
| 8192 | f64 | D48+3/D48/G6, 0.80 s, 7.3e-14 | same | D48/G3, 1.01 s, 2.2e-14 | G, 1.30 s |

(times from this run, which ran 5-10% slow throughout).  Budgets 4 and 8 pick the same plans:
nothing with growth between one level of ours (3.4) and 8 is faster than it.  One level of ours
keeps a 1.3-1.4x speedup at about a quarter of the deepest plans' error.

Library (`fmm.h`, `fmm.c` + `fmm_impl.h`, `build/libfmm.a`; `test_fmm.c`,
`results/test_fmm_2026-10-25.txt`).  `fmm_sgemm` / `fmm_dgemm(n, A, lda, B, ldb, C, ldc,
max_growth)` compute C = A B for row-major n x n matrices with the planner's choice for this
machine (optionally within an error-growth budget); plans are made once per (n, precision,
budget) and kept, and the workspace is kept between calls until `fmm_release`.  The calibration
cache is `FMM_CALIB_DIR`, default `~/Library/Caches/fmm` (bench_fmm keeps `results/`);
`fmm_calibrate(n, f64)` fills it once per machine.  Any size inside the calibrated range is
planned (below), outside it or without a calibration the classical GEMM runs, so a call is
always correct.  Calls are
serialized (each uses the whole machine).  The benchmark is now a driver on top of the library
(`bench_fmm.c` includes `fmm.c`), so both run the same code.  The test, against Accelerate's
GEMM (median of 3):

| n | f32 plan | speedup | f64 plan | speedup |
|---|---|---|---|---|
| 1000, 3000 | G | 0.99 | G | 1.00 |
| 2048 | G | 0.99 | D48/G6 | 1.18 |
| 4096 | D48/G6 | 1.12 | D48+4/D48/G6 | 1.37 |
| 8192 | D48+4/D48/G6 | 1.39 | D48+3/D48/G6 | 1.72 |
| 4096 in ld 4160 | D48/G6 | 1.06 | D48+4/D48/G6 | 1.33 |
| 8192, budget 4 | D48/G3 | 1.50 | D48/G3 | 1.27 |

All results agree with Accelerate to rounding level (f32 1e-5, f64 1e-13 relative); with an
empty cache every call runs the classical GEMM.  Limits: square matrices, C = A B (no alpha,
beta or transposes).

Sizes that are not powers of two (`results/pad_2026-10-25.txt`, `test_fmm_pad_2026-10-25.txt`).
The cost model interpolates its calibration (log-log between the measured powers of two), and a
plan runs at the smallest size N >= n its levels divide: n rounded up to a multiple of 8 * 2^j,
A and B copied into zeroed N x N matrices and the top-left n x n copied back (priced at 6 N^2
elements of traffic); Accelerate's GEMM needs no alignment (within 5% off multiples of 16-64),
so the padding is at most a few rows.  Against the best classical variant:

| n | f32 plan | speedup | f64 plan | speedup |
|---|---|---|---|---|
| 3000 | D48/G6 | 1.08 | SW+4/D48/G6 | 1.26 |
| 5000 | SW+4/D48/G6 | 1.20 | D48+4/D48/G6 at 5008 | 1.43 |
| 6000 | SW+4/D48/G6 | 1.29 | D48+4/D48/G6 | 1.54 |
| 7000 | SW+4/D48/G6 | 1.36 | D48+4/D48/G6 at 7008 | 1.56 |
| 9000 | D48+4/D48/G6 at 9008 | 1.52 | D48+4/D48/G6 at 9008 | 1.66 |
| 10000 | D48+4/D48/G6 | 1.66 | D48+4/D48/G3 | 1.72 |
| 12000 | D48+4/D48/G6 | 1.55 | SW/D48+4/D48/G6 | 1.79 |

Predictions within 5% at most sizes (8-13% pessimistic at 9000-10000 f64), results correct.

Which rank-48 program (`results/orig315_2026-10-25.txt`; `make build/bench_fmm_orig`,
`build/bench_fmm_acc`, `gen_kernels.py --dps48 PREFIX`).  Our 201-operation point, PLinOpt's
original rational scheme (315 operations) and its accurate variant (284) run at the same speed
as fused passes: totals within 1% (alternating runs, three each); the 315-operation passes take
2-8% longer, about 0.3% of the total, because the passes are bound by memory traffic, not
arithmetic.  They differ in accuracy, at the same speed:

| 8192 | ours, 201 | original, 315 | accurate, 284 |
|---|---|---|---|
| f32, one level (D48/G3) | 1.14e-5 | 5.55e-6 | 5.14e-6 |
| f32, two levels (D48+4/D48/G6) | 4.19e-5 | 8.13e-6 | 6.38e-6 |
| f64, one level | 2.20e-14 | 1.15e-14 | 9.32e-15 |
| f64, two levels | 7.29e-14 | 1.35e-14 | 1.01e-14 |

One level of ours has twice the error of the others and two levels five to seven times: its
error grows by about 3.4 per level, the accurate scheme's by about 1.4.  So for this library
the operation count our search minimized has no value, and the accurate scheme is strictly
better (same speed, a fraction of the error, and under an error budget it admits deeper,
faster plans).  For practice the objective to optimize in the class is the error growth (the
size of the coefficients and of the intermediate sums), not the operation count.

The library's D48 level is the accurate DPS program (2026-10-25; `results/accuracy_accurate_2026-10-25.txt`,
`calib_accurate_2026-10-25.txt`, `test_fmm_accurate_2026-10-25.txt`).  D48 is named for Dumas,
Pernet and Sedoglavic, whose rank-48 scheme (arXiv:2506.13242) every program here belongs to;
the kernels now come from their accurate rational program (PLinOpt's 4x4x4_48_accurate, 284
operations) and the calibration cache records which program it was measured with.  Same plans
and speed as before (16384 f32 D48+3/D48/G6 1.68 s, 8192 f64 D48+4/D48/G6 0.80 s, 16384 f64
SW/D48+4/D48/G6 5.71 s predicted); the error model's factor per D48 level drops from 3.4 to 1.20
(f32) and 1.13 (f64), so under any budget down to 2 the fastest plan qualifies.  Measured at
8192 / 16384 f32 the fastest plans' error against an f64 product, 4.47e-6 / 6.87e-6, is below
the classical f32 GEMM's own (4.61e-6 / 7.23e-6): the products are shorter dot products.  f64
8192: 1.01e-14 (was 7.29e-14).  test_fmm passes (8192 f64 1.70x, 9000 f64 1.73x over Accelerate).

Rust (`rust/`, crate `fmm`; `results/rust_pass_2026-10-25.txt`).  Feasibility of a Rust library
with as little unsafe code as possible: the fused passes in safe Rust (`gen_kernels.py --rust`
emits them from the same programs) over Accelerate's GEMM, whose three FFI declarations
(`cblas_sgemm$NEWLAPACK`, `cblas_dgemm$NEWLAPACK`, `BLASSetThreading`, behind safe wrappers
that check the slices) are the crate's only unsafe code.  The kernels cut every slice to the row
length first, so no bounds checks remain, and take each slice as a separate parameter: Rust tells
the compiler that &mut parameters overlap nothing, which vectorizes the loop as restrict does in
C (slices inside an array argument carry no such promise and the loop stayed scalar).  The D48
left-factor pass, 64 streams:

| pass | safe Rust | C kernel, same threads | C library (GCD) |
|---|---|---|---|
| 8192 f32 | 9.7 ms | 9.6 ms | 9.0 ms |
| 8192 f64 | 19.9 ms | 19.5 ms | 18.4-19.0 ms |
| 16384 f32 | 37.6 ms | 36.5-38.1 ms | 36.2 ms |
| 16384 f64 | 75.2 ms | 76.6 ms | 74.3 ms |

The safe Rust kernel matches the C kernel (within 3%, outputs bit for bit identical); the 1-8% to
the C library is the thread driver (a thread spawned per pass and a fixed split of the rows
against GCD's pool and 64 chunks), not the kernel; a persistent pool with dynamic chunks should
close it, and the passes are about 10% of the run time anyway.  Accuracy is identical by
construction (same operations in the same order; Rust contracts nothing into fused
multiply-adds).

Accuracy measures compared (2026-10-25; `growth.py`, `results/accuracy_exact_2026-10-25.txt`).
Dumas, Pernet and Sedoglavic (arXiv:2603.18699v3; Table 1 of that paper is our D48, PLinOpt's
4x4x4_48_accurate) measure accuracy in two ways.  The first is a worst-case bound from the
[L; R; P] matrices alone: the (p, q)-growth factor
gamma_{p,q} = || ( sum_i ||L_i||_{q*} ||R_i||_{q*} |P_ji| )_j ||_p.  The forward error after l
levels is at most O(gamma^l) ||A||_q ||B||_q u; they favour p = inf, q = 2.  The second is the
max-norm error against the exact product on normal inputs at n = 32-512.

Our measure grew out of the harness's correctness check: the max-norm difference from
Accelerate's classical product in the same precision, relative to max |C|, on uniform inputs.
The accuracy budget fitted a factor per level to it.  `growth.py` computes the growth factors from
the straight-line programs our kernels are generated from, checks each scheme against the matrix
multiplication tensor first, and reproduces the paper's Table 2 exactly for Winograd (our SW: 18 /
8 / 31.241 / 14 in (inf,inf) / (inf,2) / (2,inf) / (2,2)), Strassen, DPS25 rational (288 / 38.16
/ 1032 / 139.9) and Table 1 accurate (148 / 25.46 / 514.9 / 91.21).  Our 201-operation point,
not in the paper, is worst in every norm (399 / 75.85 / 1072 / 225.9; exponent log4 gamma_{inf,2}
3.12 against 2.34).

In f32 against an f64 product of the same inputs (effectively exact; bench_fmm `FMM_EXACT=1`;
`FMM_NORMAL=1` for normal inputs), the error as a multiple of the classical f32 GEMM's own, at 8192:

| scheme | gamma_{inf,2} per 4x | 1 level | 2 levels | 3 levels |
|---|---|---|---|---|
| Table 1 accurate | 25.5 | 0.89 / 0.82 | 0.97 / 0.94 | 1.42 / 1.41 |
| DPS25 rational | 38.2 | 1.02 / 0.92 | 1.51 / 1.53 | 2.93 / 2.92 |
| our 201 | 75.9 | 2.47 / 2.72 | 9.09 / 7.97 | 34.5 / 32.2 |
| Winograd, two binary levels per 4x | 64 | 2.91 / 2.90 | 9.59 / 8.84 | |

The table shows uniform / normal inputs.  At 4096 the picture is the same.  Within each scheme
the classical and Winograd rows are identical across the three builds.

- The ranking is the paper's gamma_{inf,2} ranking, as their Figure 1 found.
- Once the leaves are small, the growth per level tracks gamma_{inf,2} / k^2 to within a factor
  0.76-0.94: 1.47-1.50 measured against 1.59 predicted for Table 1, 1.92-1.93 against 2.39 for
  DPS25, 3.8-4.0 against 4.7 for ours, and 3.1-3.3 against 4.0 for Winograd.  The divisor k^2
  appears because each level splits A and B into k^2 blocks of 1/k^2 of the squared 2-norm.
- On the first levels the leaf GEMM's own error dominates.  One or two levels of Table 1's
  scheme are as accurate as the classical GEMM, or more so (0.82-1.11), because its products are
  4x shorter dot products.

Two consequences:
- Our calibration's measure, the difference from the classical product, includes the classical
  GEMM's own error.  It is right for schemes much worse than classical (ours: 8.3e-6 against
  8.4e-6 exact), but overstates accurate ones by 1.1-1.4x (Table 1 at 8192: 5.14e-6 against
  4.12e-6 for one level, 6.38e-6 against 4.47e-6 for two).  That is the safe side for a
  budget, but too blunt to rank accurate schemes.  In f64 there is no exact reference yet.
- A more accurate scheme pays only at depth (three or more levels, small leaves) or in low
  precision.  At the library's one or two levels in f32, Table 1's scheme is already at
  classical accuracy.

Search for more accurate schemes (2026-10-25; `matmul/dps48/gamma/`, `src/bin/gamma48.rs`,
`results/gamma_search_2026-10-25.txt`).  The search space is Table 1's orbit under the De Groot
isotropies (U, V, W) in GL(4)^3, together with the three role assignments of the scheme's cyclic
symmetry.  gamma_{inf,2} treats L and R alike (row 2-norms) and P differently (the max over
outputs), so the role, i.e. which factor set computes the outputs, matters: Table 1's three roles
give 25.456, 32.97 and 28.14, and the published one is already the best.

The objective is minimized from many random starts: a smoothed max and absolute value, BFGS with
continuation, then an exact minimax polish.  It ran first in Python (scipy, 12 processes), then as
the Rust binary `gamma48`.  `gamma48` uses the exact adjoint gradient (checked against finite
differences to 1e-10), runs 240 starts in 8 s against Python's 230-270 s, and finds the same
optima.

- Orthogonal U, V, W keep gamma_2 at its minimum (154.51) and leave V without effect.  The
  minimum there is 16 sqrt2 = 22.627 for the published role and 12 + 8 sqrt2 = 23.31 for the
  others.
- Over the whole orbit, 30,000 starts on Table 1 and 7,200 each on DPS25 and on our 201-operation
  point all reach the same optima: the three schemes share one orbit.  The lowest value,
  21.4073, is found thousands of times and nothing lower ever appears.  At that point one factor
  has singular values (1, 1, s, s) with s = 2(sqrt2 - 1), so the coefficients lie in Q(sqrt2).
  They cannot be dyadic: s enters R and 1/s enters P.
- The dyadic orthogonal sub-orbit was enumerated exhaustively.  The group G of orthogonal 4x4
  matrices with entries in Z[1/2] or Z[1/2]/sqrt2 has 2304 elements (W(F4), plus the 1152
  matrices with entries 0 and +-1/sqrt2), and every (U, V, W) in G^3 gives a dyadic scheme
  after per-term rescaling.  Both growth factors are unchanged by signed permutations on the
  left, so there are 216 distinct points per role.  The 16 sqrt2 point with gamma_{inf,inf} 132
  is the unique best in both factors.

The scheme at that point (`matmul/dps48/gamma/g16s2_{L,R,P}.sms`) turned out not to be new.  It is
PLinOpt's `4x4x4_48_accurate_262` (DPS's 262-operation accurate variant, published in PLinOpt on
2026-10-13 and cited for its operation count in arXiv:2609.12027 v2).  `equiv262.py` maps one onto
the other through the input-swapping symmetry (X, Y, Z) -> (Y^T, X^T, Z^T), signed permutations of
U, V, W, and a relabelling and rescaling of the products.  We rediscovered it; to our knowledge its
growth factors and measured accuracy have not been reported, and the paper's Table 1 is still
presented as the accurate variant.  It is exact over Z[1/2], checked exactly
and by PLinOpt's SLPchecker; PLinOpt's programs `slp/g16s2o_*` take 445 operations: 339 additions
and 106 multiplications by 2, 1/2 or 1/4.  Against Table 1: gamma_{inf,2} 22.627 against
25.456, gamma_{inf,inf} 132 against 148, gamma_{2,2} 90.51 against 91.21, and gamma_2 154.51 for
both.  In f32 against an f64 product (4096 and 8192, uniform and normal inputs) its error is
0.74-0.86 of Table 1's at one level, 0.75-0.81 at two and 0.72-0.85 at three.  At the library's
one or two levels that is 0.66-0.83 of the classical f32 GEMM's own error.  Speed is unchanged: alternating runs of the library's plans
(4096 D48/G6, 8192 D48+4/D48/G6) and of single levels, f32 and f64, give 1.000-1.028 of Table 1's
time at the best of three rounds.  The passes are bound by memory traffic, so 445 against 284
operations does not show.

The gamma_{inf,2} optimum itself does not pay.  The 21.407 scheme, with gamma_{inf,inf} 176.6
and constants that round, measures level with Table 1 (0.98-1.01 at three levels).
gamma_{inf,2} alone is not the objective.  What paid was improving gamma_{inf,2} and
gamma_{inf,inf} together while staying dyadic, so that multiplying by the scheme's constants is
exact.

The library's D48 level is now DPS's 262-operation program (2026-10-25, PLinOpt's
`4x4x4_48_accurate_262`; results in `results/calib_262_2026-10-25.txt`,
`test_fmm_262_2026-10-25.txt`, `rust_262_2026-10-25.txt` and `accuracy_262_2026-10-25.txt`).
- The plans and speed are the same.  Predicted: 16384 f32 D48+2/D48/G6 1.68 s, 8192 f64
  D48+4/D48/G6 0.80 s, 16384 f64 SW/D48+4/D48/G6 5.74 s.
- The library plans' error against the exact reference is 0.67-0.81 of the 284-operation
  program's.  At f32 16384 it is 4.6e-6 against 6.3-6.9e-6, 0.64-0.65 of the classical f32 GEMM's
  own error, which was 0.89-0.95.  At f64 8192 it is 6.5e-15, 0.77-0.79 of the classical error.
- The error model's factor per D48 level is now 1.04 (f32) and 1.02 (f64).
- test_fmm is all ok (8192 f64 1.66x, 16384 f64 1.93x over Accelerate), and the Rust crate
  matches C bit for bit (crosscheck 18/18).
- `build/bench_fmm_acc284` keeps the previous program, the paper's Table 1 scheme.

Paper (2026-10-25): `doc/matmul_4x4_rank48_accurate262.tex` / `.pdf`, "The 262-operation <4x4x4:48>
algorithm is also the more accurate one".  Its growth factors are exact in Q(sqrt2) and agree with
PLinOpt's `growthfactor`.  The other rational classes were searched as well: Li-Wang-Hu members
s(2^k), k = -2..3, and Agarwal's scheme.  Their gamma_{inf,2} minima rise from 21.41 (t = 1/4, the
DPS class) through 23.14, 25.17, 27.85, 32.68 to 40.13, with Agarwal's at 39.62, so none reaches
22.63 (`results/gamma_classes_2026-10-25.txt`).

Accuracy campaign (`results/accuracy_campaign_2026-10-25.txt`):
- The setting: f32 and f64, n = 4096 and 8192, uniform and normal inputs, 3-5 seeds.  The f64
  reference is compensated dot products (bench `dd_gemm`).
- The 262 variant's error is 0.75-0.77 of Table 1's on average, 0.62-0.90 per instance, at the same
  speed (0.977-1.007).
- Two dyadic probe points, each worse than Table 1 in one growth factor, still beat Table 1.  The
  measured order of the dyadic schemes is the Q0 order (80, 94, 144, 180).  The Q(sqrt2) point,
  whose constants round, measures like Table 1.

Deep recursion at n = 1024, 1-5 levels down to scalars (`results/accuracy_deep_2026-10-25.txt`):
- The 262/Table 1 ratio falls from 0.80 at one level to 0.72 at five.
- From four levels to five the errors grow 2.60 against 2.78 per level.
- The program matters at depth: the same scheme with 445-operation programs is worse than Table 1.

Why programs differ (2026-10-25; `matmul/dps48/gamma/slp_errmodel.py`,
`results/slp_errmodel_2026-10-25.txt`, paper Table 8).  A first-order rounding model of one
level: each addition (and each scaling by a non-power of two) rounds with error proportional to the
exact value; inputs i.i.d., so every intermediate's size, cancellation included, is an exact
second moment.  Program length and rounding-chain length do not explain the measured errors: DPS's
262-operation programs have the longer chains (22 roundings through a level against 18 for our
445), and the probes' direct sums (37, 39) beat our programs.  The P pass does: for
accurate_262, L+R add the same error in both programs (5.74 / 5.61) but P adds 3.09 against 8.22.
Each of DPS's outputs collects 15 roundings of RMS size 0.80 of the output (partial sums cancel
early); each of ours collects 36 (more sharing between outputs) of size 1.39.  Among the four
programs whose schemes amplify leaf errors equally (2 sqrt2), the model's worst-output error orders
the measured errors exactly at three and five levels.  The direct sums' 3/4 multiplications are
negligible (11.14 vs 11.09).  Next: an accuracy-aware program optimizer (the model runs in well
under a second per program).

Optimizer sweep (2026-10-26; `matmul/dps48/gamma/optsweep.sh`, `optsweep_score.py`,
`results/optimizer_sweep_2026-10-26.txt`, best programs `gamma/slp/sweep_{dps,ours}_{L,R,P}.slp`):
PLinOpt's optimizer with 1000/5000 loops, -N, -A, and P direct or transposed, on both schemes.
Best complete sets 348 (DPS's scheme) and 409 (ours) vs DPS's published 262 and our 445; -E never
finishes in 120 s.  So the 262 programs did not come from `optimizer` alone (recipe not in the
commit; prune.sh/mirabelle.sh or hand work are candidates).  Direct P optimization gives P
programs with DPS's structure (15 roundings per output, size 0.81-0.88, P error 3.15-3.40 vs
3.09): our 445's bad P pass (8.22) came from the transposition pipeline, not the optimizer.  L+R
still worse (7.05-7.39 vs 5.74); best sets model at 8.95 / 9.96 worst-output vs 12.51 / 7.22.  Not
benchmarked.  Optimizer speed (profile of a single-threaded run: 47% malloc/free, 17% Givaro
ctor/dtor/compare, 12% GMP; RemOneCSE 77% inclusive, its per-CSE transpose 21%): machine-word
field 3.4-4.3x (measured with Modular<int64_t>), dropping the transpose 1.2-1.4x (measured),
distinct thread seeds 1.25x typical / 1.75x worst (20% of 14 threads share a clock seed), loop
reuse <= 1.2x (estimate), -E needs memoization (not a factor); parallel efficiency 57% at 10
threads, 43% at 14, same with machine words.  Scratch builds only, nothing sent upstream.

PLinOpt optimizer speed, as commits (2026-10-26): branch `optimizer-speed` of the fork
github.com/gsidebottom/plinopt (remote `fork` in matmul/dps48/plinopt, base upstream main 7c20065;
local only until pushed), one PR-sized commit per item, each verified byte-identical with `-s 1`
where it should be, SLPchecker on every program, upstream's bin/FDT.sh (its own failures are
clock-random, 0-5 of ~1860):
1. 193fb48 one generator per thread, reseeded per random loop from a global seed; `-s #` fixes
   it; ties broken by lowest loop index; compacter reseeded -- output byte-identical across runs
   and OMP_NUM_THREADS = 1, 3, 5, 14 (item 3: a mean 20% of 14 clock-seeded threads repeated
   another's draws).
2. 965b0ed RemOneCSE without the per-CSE transpose: L 1.50 -> 1.06 s, R 3.08 -> 2.33, P 2.83 ->
   2.38 (-O 200, single thread, best of 3).
3. 3297fb1 OneSub returns false when exhausted (no redundant rebuild): 2-3%.
4. a6b3eaa RemOneCSE direct row test + incremental pair-map updates: 1.29x / 1.48x / 1.69x;
   cumulative over upstream 1.79x / 1.91x / 1.99x.
5. f54f80f `-Q`: search over Modular<int64_t> (p = 4294967291), constants lifted by rational
   reconstruction (int64 Euclid, per-thread cache), program checked over Q, fallback to the
   rational search: 3.9x / 4.4x / 4.8x over commit 4, 7.1x / 8.7x / 9.7x over upstream; 207/207
   data files correct, 4 fall back (DPS-integral/intermediate 2x2x2 schemes, big coefficients);
   FDT gains a -Q pipeline.  (First version was 4-7x SLOWER: a 46k-iteration bound loop and GMP
   rationals in every Fabs/Fsign; fixed before committing.)
6. 87002e8 memoized exhaustive search `-E` with budget `-B` (canonical state key = temporaries' linear
   forms over the inputs; replay of the best choices): same optima as the old -E where it finishes;
   3x4x7_63_rational_L 72 additions vs 84 from -O 1000 (old -E never finishes); on the 48x16
   <4x4x4:48> matrices no better than random restarts (see the commit message).
Harness: matmul/dps48/plinopt_dev/{build.sh,bench.sh}; results/plinopt_optimizer_speed_2026-10-26.txt.

Realized-program accuracy search (2026-10-26; `src/bin/slpopt.rs`: the rounding model in Rust,
validated digit for digit against slp_errmodel.py; programs as DAGs; `score`, `search` (simulated
annealing over form-preserving moves, `--check`), `construct` (greedy model-scored CSE)).  Headroom
for accurate_262's scheme (DPS's programs model at worst 7.22): PLinOpt's random programs
(`optimizer -Q -D -O 1 -s k`, 3000 per matrix, scored with the other two fixed) give R 6.56, L
7.27 (one program), P 7.22; other PLinOpt methods no better; greedy construction worse; annealing
barely moves from good starts.  Candidate opt1 = DPS's L + polished sampled R + greedy P
(`gamma/slp/opt1_*`), modelled 6.47.  MEASURED (campaign_var.sh / summarize_var.py,
results/accuracy_opt1_*, accuracy_deep_opt1_*, speed_opt1_*, opt1_summary_2026-10-26.txt): ratios
to accurate_262 1.001 / 1.007 / 1.014 at 1-3 levels (n = 4096, 8192; within the seed spread
0.82-1.15), 0.95 at 4-5 levels (n = 1024), speed 0.97-1.01.  So an 11% smaller modelled pass error
is invisible where the leaf GEMMs' error dominates and worth ~5% at depth: for this scheme the
program lever is nearly exhausted; a measurable gain needs a scheme with lower leaf amplification
(amp 2.83 = 2 sqrt2 is the scheme's) or a change at the precision level (compensated passes, at a
time cost).

Scheme-level lever, option 1 (2026-10-26): (a) all 648 dyadic orthogonal points scored by the
realized model with greedy programs (`dyadic_points.py`, `slpopt realized`,
results/dyadic_points_realized_2026-10-26.txt): amp takes five values, min 2 sqrt2 at 342 points
incl. accurate_262's; realized pass error 6.7-8.6, accurate_262's point 6.96, lowest 6.73 (probe
B's family) -- not measurable with equal amp; (b) ampwalk.py (SA over non-orthogonal dyadic
isotropies) and ampmin.py (continuous BFGS, 12 starts) both stay at 2.8284 = 2 sqrt2 at orthogonal
points (results/amp_floor_2026-10-26.txt): 2 sqrt2 is the orbit's minimum amplification.  The
Q(sqrt2) gamma_{inf,2} minimum has amp 3.14 (lower gamma != lower amp).  Conclusion: inside
accurate_262's orbit no scheme beats it on the dominant term; the other known orbits are
worse on it too (ampmin.py over matmul/dps48/classes/, results/amp_classes_2026-10-26.txt: LWH
s(1/4) = the DPS class 2.83, s(1/2) 3.00, s(1) 3.54, s(2) 4.50, s(4) 6.01, s(8) 8.25, Agarwal
5.80).  What remains is the precision level: compensated passes at a time cost, or
low-precision targets where the pass error is a larger share.

Off the known orbits (2026-10-26; `ampvariety.py`, `inspect_point.py`,
results/amp_variety_2026-10-26.txt): the amplification minimized over the whole variety of rank-48
decompositions (soft max + penalty on the Brent equations, L-BFGS, analytic gradients).  From
accurate_262 perturbed by 0.02-1.0 of the coefficient size (16 starts) every run returns to
2.8284 with all 16 outputs equal, at generic points of the orthogonal sub-orbit (gamma_2 154.51,
dense irrational coefficients); from LWH s(1/2) it descends off that orbit to the same 2.8284;
from Agarwal's scheme the penalty balance failed (large coefficients), inconclusive.  So 2 sqrt2
is a local minimum of the variety around everything we can reach, not only of the orbit: option
1 (a scheme with lower leaf amplification) finds nothing, and the realized-program target can
only move through the passes' arithmetic.

f64 PASSES ON THE f32 PATH (2026-10-26, 2f31dc1; FMM_F64PASS=1): gen_kernels.py emits
dps48_{L,R,P}_fd (float blocks, double arithmetic), fmm_impl.h selects them for D48 levels of
the float instantiation when the switch is set.  MEASURED (campaign_f64pass.sh, results/
accuracy_f64pass_*, accuracy_deep_f64pass_*, speed_f64pass_*, f64pass_summary_2026-10-26.txt),
error ratio to the f32 passes: main campaign (n = 4096, 8192) 0.987 / 1.015 / 0.977 at 1-3
levels (a tie, as predicted: leaf error dominates); deep n = 1024: 0.974 / 0.962 / 0.849 / 0.721
/ 0.639 at 1-5 levels (f32 error/classical 9.79 -> 6.25 at five levels); speed 1.000-1.017 at
4096/8192 (D48/G, D48/G6, D48+4/D48/G6), 1.057 on D48+2/D48/G6 at 16384, 1.000 on D48/G there.
The first realized change that lowers Figure 2's line: the model's floor is the GEMM interface
roundings (worst 4.1 vs 7.2), and the measured 36% at five levels is in line with that.
Open: make it the default (costs <= 2% below 16384; the 16384 deep plan pays 6%); add the switch
to the Rust port; the paper.

SEDOGLAVIC'S QUESTIONS (2026-10-26, on the pushed draft 4657bfe): what the "rounding-chain
factor" is, and the gamma_{inf,2} = 21.4073 decomposition.  (1) Q0 is PLinOpt's own combinatorial
factor (growthfactor): a term count, not a chain length; Section 2.1 had been corrected (e329ca1)
but the name survived in the abstract and introduction, now "PLinOpt's combinatorial factor".
(2) The point was public but unnamed in the paper: slp/g214d_{L,R,P}.slp (the measured direct
sums, rounded constants) and rs_table1_r{1,2}.txt (line 1: the search's (U, V, W) that reach it
from accurate in roles 1 and 2).  `exact_q214.py` snaps g214d to a + b sqrt2, a, b in Z/4 (unique;
residuals <= 1.2e-8), checks the Brent equations exactly in Q(sqrt2) and writes
g214_exact_{L,R,P}.txt ("row col a b") and the listing g214_exact.txt: L 304 x +-1/2; R 192 x
+-1/2, 192 x +-(sqrt2 - 1); P 80 x +-1/2, 40 x +-1, 24 x +-2, 16 x +-(1 + sqrt2)/4, 56 x
+-(1 + sqrt2)/2, 24 x +-(1 + sqrt2).  Every |R_i|^2 = 13 - 8 sqrt2 and every |L_i|^2 is rational,
so gamma_{inf,2}(j) = (8 + 6 sqrt2) sqrt(13 - 8 sqrt2) = 2 sqrt(58 + 40 sqrt2) = 21.40734 on all
16 outputs (degree 4 over Q; the search's 21.4073438 is its tolerance), gamma_{inf,inf} = 120 +
40 sqrt2 = 176.57; gamma_{2,inf} 583.75, gamma_{2,2} 85.63, gamma_2 157.25, Q0 146, amp 3.135:
Table 1's row and Section 8.2's 3.14.  Paper: Section 4.2 gives the exact point; Section 8.2
says amp_j is the root-sum-square counterpart of gamma_{inf,2}'s per-output sum (the 21.41
point minimizes the sum, 21.41 vs 22.63, not the root-sum-square, 3.14 vs 2.83, which is why the
smallest growth factor did not measure best); the Data section names the files.

Q0 CORRECTED AND THE EQUATIONS NUMBERED (2026-10-27).  Sedoglavic's second message answered
Greg's question on how accurate_262 was found (accurate = the orbit's gamma_2 minimum, unique
modulo orthogonal isotropies by their convexity result, found numerically with pymanopt over the
quotient of GL_4 by the orthogonal group, DPS26b Lemma 27; then Touko Ursin explored Hadamard
matrices to lower gamma_{inf,2}) and asked for numbered equations, pointing at "section 2.1,
unnumbered equation" (the growth-factor bound).  Locating it exposed a real error: DPS define
Q0 = max_j(nnz(P_j) + max_{i: p_ji != 0}(nnz(L_i) + nnz(R_i))) (ISSAC 2024 Th. 12, JSC 2026
Th. 18, after Ballard et al. 2016 Def. 1; their ISSAC table has Winograd 10, Strassen 8, their
accurate 2x2 variant 15), but PLinOpt's growthfactor (include/plinopt_norms.inl, cf85c3f May
2026, unchanged at 7c20065) computes the PRODUCT nnz(L_i) nnz(R_i) + nnz(P_j) and prints
13/8/23 -- and the paper's Q0 column, Sections 1, 2.1, 3, 5.2, 7 and the Oct 27 reply to
Alexandre had copied the tool's numbers (80/180/152/101/146, probes 144/94) and called them DPS's
Q0.  Fixed: Section 2.1 defines Q0 as DPS do (eq. 3), says what it counts (Q0 - 3 additions and
one multiplication feeding the worst output), and names the tool's quantity the term count T0
(eq. 4) with the Winograd discrepancy stated; Table 1 and Table 5 (paper_acc262.py FACT
constants, regenerated, only that column changed): Winograd 10, Strassen 8, DPS-accurate 15,
rational 48, accurate 46, accurate_262 34 (still the smallest, bold kept), Q(sqrt2) point 42,
201 38, probe A 40, probe B 46.  Section 7 now says Q0 does NOT order the dyadic schemes'
measured errors (34, 46, 40, 46) while T0 does (80, 94, 144, 180) on those four points.
Every display equation is numbered, (1)-(12): bilinear identity, gamma_{p,q}, Q0, T0, the
isotropy action, its matrix form, the trace form, Q_{U,V,W}, product 32's B side, the adjoints,
the exact gamma_{inf,2}, amp_j.  Citations: the growth factor is DPS26b Def. 11 (Th. 18 is
the error bound); Ballard et al. 2016 added; Sedoglavic26b (27 Oct) cited in the introduction's
provenance paragraph, Section 4.2 and the acknowledgments.  20 pages.  Still to do: tell
Alexandre the Oct 27 reply's point 1 was wrong (it attributed the product formula to him);
tell Dumas the one-line fix (norm0(L[i]) + norm0(R[i])), e.g. with the optimizer-speed letter.

The Rust port (2026-10-25; `rust/README.md`; `results/rust_vs_c_2026-10-25.txt`,
`rust_crosscheck_2026-10-25.txt`, `rust_pass_pool_2026-10-25.txt`, `rust_calib_2026-10-25.txt`).
The whole library in Rust, module for module:
- `plan.rs`: plans.
- `calib.rs`: the calibration and its cache, in the C library's file format, so either library
  reads the other's cache.
- `planner.rs`: the planner, with pipelines, the error budget and padding.
- `exec.rs`: the executor. Passes run as row chunks on a rayon pool; GEMM streams and pipelined
  passes run as tasks on the same pool.
- `measure.rs`: the calibration's measurements.
- `lib.rs`: the entry points `sgemm`, `dgemm`, `plan`, `calibrate` and `release`.

Binaries: `fmmcal` fills the cache, `fmmbench` runs test_fmm's cases, and, behind the feature
`cbench`, `passbench` and `crosscheck` run against the linked C library.  Unsafe code is limited
to the FFI declarations in `sys.rs` (Accelerate's two GEMMs and its threading switch, and the
threads' scheduling class), behind safe wrappers that check the slices; everything else is
`#![deny(unsafe_code)]`.  On the same cache:

- Results: bit for bit identical to the C library's, with the same plans, in all 18 cases of
  test_fmm (both precisions, 1000-9000, padded sizes, a leading dimension above n, a budget);
  the calibration's three error measurements agree to all nine digits.
- Speed: alternating rounds of test_fmm and its port, Rust/C 0.95-1.03 per case (best of two
  rounds each, geometric mean 0.99); "over Accelerate" is against its best time in all runs:

| case | C | Rust | Rust/C | over Accelerate |
|---|---|---|---|---|
| f32 4096 D48/G6 | 37.6 ms | 36.9 ms | 0.98 | 1.14x |
| f32 8192 D48+4/D48/G6 | 0.240 s | 0.238 s | 0.99 | 1.39x |
| f32 16384 D48+3/D48/G6 | 1.726 s | 1.694 s | 0.98 | 1.60x |
| f64 2048 D48/G6 | 17.8 ms | 18.2 ms | 1.02 | 1.16x |
| f64 4096 SW+4/D48/G6 | 0.1205 s | 0.1190 s | 0.99 | 1.41x |
| f64 8192 D48+4/D48/G6 | 0.815 s | 0.814 s | 1.00 | 1.64x |
| f64 9000 D48+4/D48/G6 at 9008 | 1.043 s | 1.016 s | 0.97 | 1.78x |
| f64 16384 SW/D48+4/D48/G6 | 5.818 s | 5.835 s | 1.00 | 1.99x |

- Passes: on the rayon pool the Rust pass driver is within 0.2-2.7% of GCD; the feasibility
  test's thread per pass was 1-8% behind.
- Calibration (three C and three Rust calibrations, alternating; the third Rust one after the
  fix below): each library repeats itself to 2-4% per group of entries.  Rust is slower on small
  passes (SW blocks of 256: 1.9-3x; 512: 1.4x; D48 256: 1.3-1.5x), the pool's dispatch where a
  pass takes 0.1 ms, and 2-12% faster on SW passes from 4096 and D48 passes from 2048; GEMMs
  inside a level and pipelines agree within 4%.  With the leaves
  timed where the library runs them (see the traps below), the lone GEMMs agree with C's
  (geometric means 0.98-1.00).  The exception is f32 4096 at 1.15, a size whose GEMM runs at
  either 42 or 48-50 ms.  The Rust-made cache's plans then differ from the C-made one's only in
  the pipelines' pass threads (2-3 against 3-4), a choice in which the C calibrations also vary
  among themselves.  The Rust library on its own cache, against on the C-made cache, alternating:
  0.98-1.02 per case (16384 f32 D48+2 1.6% faster than D48+3; 4096 and 8192 f64 three pass
  threads 1% faster than four).

Traps on the way:
- A zeroed Vec gets its pages from the system only on first write.  The first Rust calibration
  therefore timed page faults into the largest sizes, where a single run is timed (SW passes at
  8192 +35%, one GEMM at 16384 +10%).  Timed buffers are now written first, as C's memset does.
- A lone multi-threaded GEMM issued right after work on the rayon pool runs 15-25% slower once
  GEMM streams have run on the pool (f32 2048 6.2-6.9 ms against 5.1 ms), and stays slower.
  The same GEMM after work on fresh scoped threads runs at full speed.  The first Rust
  calibration timed the lone GEMMs on the pool after an eviction on the pool, so it overstated
  them by 15-20% and picked D48/G6 over the classical GEMM at 2048 f32.  The leaves are now
  timed where the library runs a classical plan, on the calling thread, after an eviction by
  scoped threads.  For the same reason fmmbench runs its Accelerate reference on the main
  thread, as test_fmm does; on a pool thread it read up to 20% slow.  The cause is not
  established: SME state left on pool threads that ran streams was tested and not confirmed.
  The C library does not show it; GCD's threads park at once, where rayon's spin a while before
  sleeping, which may be the difference.
  `examples/gemm_after_level.rs` and `examples/reference_after_fmm.rs` reproduce it.

Engineering lessons (each worth a large factor, each easy to miss):

- The compiler did not vectorize the 64-stream fused loops (it gave up on overlap checks);
  `#pragma clang loop vectorize(assume_safety)` fixed it: 4.3x on the passes.
- Scratch blocks of power-of-two size all start at one offset modulo the cache's set span,
  so element c of all 64 streams maps to one cache set; padding the blocks by 1040 elements
  gave another 2.5x.
- Compare against the best classical variant, with interleaved repetitions: Accelerate's
  rate depends on block size and drifts between runs.

## Cost model: the operations that matter

For one fused level of an <g x g x g : r> scheme on n x n matrices (m = n/g):

    T(n) ~ r * T_below(m)  +  3 (g^2 + r) m^2 w / B

with T_below the time of the plan below (a GEMM, priced inside the level, or another level), w
the word size and B the achieved streaming bandwidth (120-135 GB/s in our passes, against about
270 GB/s peak).  The planner (`auto`) uses measured pass times per level type and block size in
place of the bandwidth term; predictions hold to 0.3-3% at n = 8192-16384.

Which operations matter depends on the implementation:

| implementation | what costs time beyond the products |
|---|---|
| one block operation at a time (typical libraries) | the program's operation count (what our 201 minimized) and its temporaries |
| fused streaming passes (ours) | the number of blocks read and written per level: the scheme's shape (g, r), not the point in its class |
| transforms fused into GEMM packing and epilogue | the nonzeros of L, R, P: each S_k is packed from nnz(L_k) blocks, each product feeds nnz(P column) blocks of C |

## Plan

1. **Hybrids and depth selection** (done 2026-10-24): automatic (`auto`), validated above.
2. **Calibrate and validate the cost model** (done 2026-10-24): predictions within 0.3-3% at
   8192-16384, the choice right at every tested point.
3. **Use the whole machine.**  A level's r products are independent.  GEMM streams (done
   2026-10-24): 6-14% off the best plans.  NEON products on the idle cores (tried 2026-10-24):
   at most 1-3%, fragile, not adopted.  Pipelined passes (done 2026-10-24): 8-22% off the
   deep plans; the planner chooses streams, pipelines and pass threads (2, 3, 4) per plan.
   The top levels' passes (tried 2026-10-24): two-level pipelines for three-level plans, -2.3%
   at 16384 f64, neutral or worse elsewhere, not in the planner; the top passes of two-level
   plans would need output groups that re-read their inputs (est. 1-2%).  Accuracy budget
   (done 2026-10-25): `auto:g`, from a per-level error model validated within 25%.
4. **Cheaper passes.**
   - Keep the temporaries for one product in cache instead of materializing all 48.
   - Accumulate each product straight into its C blocks (no stored M_k), trading the P pass
     for extra C traffic per product.
   - Fuse L and R into GEMM operand packing (S_k never written to memory), the "Strassen
     reloaded" approach.  Accelerate is closed, so this needs our own GEMM micro-kernel (SME2
     intrinsics on this machine) or an open GEMM (BLIS) on another machine.
   - Non-temporal stores, prefetching, and placement across the two 5-core performance
     clusters (each has its own 16 MB L2).
5. **Scheme search with practical objectives.**  Point the existing search machinery at
   the costs that matter instead of operation counts:
   - for packing-fused implementations, minimize the nonzeros of L, R, P over the class
     (Alexandre's sparsest point, 624 nonzeros against our 696, is the natural start);
   - for fused passes, prefer shapes with the best ratio of saved products to blocks moved:
     rectangular schemes (<4x4x8>), product schemes (<8x8x8:336> = ours x Strassen), 3x3:23
     for sizes 3^k * m;
   - register pressure (live values) of the fused program, if the passes ever become
     compute-bound.
6. **Other machines and precisions.**  x86-64 with MKL and BLIS (AVX-512, AMX), the Apple
   GPU (Metal Performance Shaders) and NVIDIA tensor cores; bf16/fp16, where error growth
   matters (we measured about 2x error per level: f32 relative error 5e-6 one level, 1.6e-5
   for our 4x4 level, 3.7e-5 three levels at n = 16384).
7. **A library entry point** (done 2026-10-25): `fmm.h`, `libfmm.a`, tested against
   Accelerate; any size inside the calibrated range (interpolation and padding, done
   2026-10-25).  Rust port (done 2026-10-25): crate `fmm` in `rust/`, only FFI declarations
   unsafe; same plans, speed and results (bit for bit) as the C library.  Next for both:
   rectangular shapes, alpha / beta and transposes.

## Milestones

- M1 (done 2026-10-24): harness, correctness against classical, honest numbers.
- M2 (done 2026-10-24): hybrids measured; calibrated planner (`auto`) validated at
  2048-16384 in both precisions.
- M3 (done 2026-10-24): the whole machine: GEMM streams (6-14%), NEON products (tried, at most
  1-3%, not adopted), pipelined passes (8-22%); auto at 1.17-1.60x (f32) and 1.19-2.01x (f64)
  over the best classical variant at 2048-16384.
- M4: packing fusion prototype (own GEMM kernel or BLIS) and its gain.
- M5: practical-objective scheme search and its measured effect.
