# Practical fast matrix multiplication: plan

Started 2026-10-24.  Code and results: `matmul/fastmm/` (build with `make`; sweeps
`run_bench.sh`, `run_blocked.sh`, `run_hybrid.sh`, `run_auto.sh`, `run_probes.sh`,
`run_streams.sh`, `run_auto_streams.sh`, `run_neon.sh`, `run_neon2.sh`; results in
`matmul/fastmm/results/`).  `bench_fmm -m auto` picks the plan per size and precision from a
calibrated cost model; `bench_fmm -n N -p` prints the planner's choices.

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
   2026-10-24): 6-14% off the best plans, chosen per plan by the planner.  NEON products on the
   idle cores (tried 2026-10-24): at most 1-3%, fragile, not adopted (see above).  Next: overlap
   the passes with the GEMMs (the passes are 10-15% of one- and two-level plans and 24% of
   SW/D48/D48 at 16384 f64), watching the same L2 contention; an accuracy budget for the
   planner (error grows with depth).
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
7. **A library entry point.**  `fmm_gemm(n, A, B, C)` running the planner's choice from the
   cached calibration, with the correctness check against classical kept as a test.

## Milestones

- M1 (done 2026-10-24): harness, correctness against classical, honest numbers.
- M2 (done 2026-10-24): hybrids measured; calibrated planner (`auto`) validated at
  2048-16384 in both precisions.
- M3: the whole machine: GEMM streams (done 2026-10-24, 6-14%); NEON products (tried, at most
  1-3%, not adopted); overlapped passes; measured gain.
- M4: packing fusion prototype (own GEMM kernel or BLIS) and its gain.
- M5: practical-objective scheme search and its measured effect.
