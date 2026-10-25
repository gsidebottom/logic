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
