# Practical fast matrix multiplication: plan

Started 2026-10-24.  Code and results: `matmul/fastmm/` (build with `make`; sweeps
`run_bench.sh`, `run_blocked.sh`; results in `matmul/fastmm/results/`).

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

    T(n) ~ r * G(m)  +  3 (g^2 + r) m^2 w / B  +  overhead

with G(m) the measured GEMM time at size m, w the word size and B the achieved streaming
bandwidth (120-135 GB/s in our passes, against about 270 GB/s peak).  Recursion
multiplies the terms.  Calibrate G and B once per machine, then choose scheme and depth by
the smallest predicted T for each (n, precision).

Which operations matter depends on the implementation:

| implementation | what costs time beyond the products |
|---|---|
| one block operation at a time (typical libraries) | the program's operation count (what our 201 minimized) and its temporaries |
| fused streaming passes (ours) | the number of blocks read and written per level: the scheme's shape (g, r), not the point in its class |
| transforms fused into GEMM packing and epilogue | the nonzeros of L, R, P: each S_k is packed from nnz(L_k) blocks, each product feeds nnz(P column) blocks of C |

## Plan

1. **Hybrids and depth selection (next).**  Our 48-scheme fused on top with one Strassen
   level below (336 products of n/8; one fused 4x4 level instead of two Strassen levels),
   Strassen^2 fused plus Strassen (343), two fused 48 levels (2,304 products of n/16) for
   very large n.  Predict with the cost model first, then measure.  Prediction: the
   48+Strassen hybrid beats three Strassen levels at 16384 (fewer products and cheaper passes).
2. **Calibrate and validate the cost model.**  Measure G(m) for m = 512..8192 and B for
   k-stream passes (k = 3..64) in both precisions; target predictions within 5% of measured.
3. **Cheaper passes.**
   - Overlap the passes with the GEMMs (pass for product k+1 while GEMM k runs) and keep the
     temporaries for one product in cache instead of materializing all 48.
   - Accumulate each product straight into its C blocks (no stored M_k), trading the P pass
     for extra C traffic per product.
   - Fuse L and R into GEMM operand packing (S_k never written to memory), the "Strassen
     reloaded" approach.  Accelerate is closed, so this needs our own GEMM micro-kernel (SME2
     intrinsics on this machine) or an open GEMM (BLIS) on another machine.
   - Non-temporal stores, prefetching, and placement across the two 5-core performance
     clusters (each has its own 16 MB L2).
4. **Scheme search with practical objectives.**  Point the existing search machinery at
   the costs that matter instead of operation counts:
   - for packing-fused implementations, minimize the nonzeros of L, R, P over the class
     (Alexandre's sparsest point, 624 nonzeros against our 696, is the natural start);
   - for fused passes, prefer shapes with the best ratio of saved products to blocks moved:
     rectangular schemes (<4x4x8>), product schemes (<8x8x8:336> = ours x Strassen), 3x3:23
     for sizes 3^k * m;
   - register pressure (live values) of the fused program, if the passes ever become
     compute-bound.
5. **Other machines and precisions.**  x86-64 with MKL and BLIS (AVX-512, AMX), the Apple
   GPU (Metal Performance Shaders) and NVIDIA tensor cores; bf16/fp16, where error growth
   matters (we measured about 2x error per level: f32 relative error 5e-6 one level, 1.6e-5
   for our 4x4 level, 3.7e-5 three levels at n = 16384).
6. **A library entry point.**  `fmm_gemm(n, A, B, C)` choosing scheme and depth from the
   calibrated model, with the correctness check against classical kept as a test.

## Milestones

- M1 (done 2026-10-24): harness, correctness against classical, honest numbers.
- M2: hybrids measured; cost model calibrated and predicting within 5%.
- M3: pass overlap and product accumulation into C; measured gain.
- M4: packing fusion prototype (own GEMM kernel or BLIS) and its gain.
- M5: practical-objective scheme search and its measured effect.
