# fastmm: fast matrix multiplication on Apple silicon

A C library (`fmm.h`, `build/libfmm.a`) and a Rust crate (`rust/`, crate `fmm`) that compute
C = A B for large row-major f32 or f64 matrices faster than Apple Accelerate's GEMM, by running
the recursion levels of fast matrix multiplication schemes as fused streaming passes over
Accelerate GEMM leaves, with a planner that picks the plan for the machine, shape and precision
from a calibration, under an error budget.  Measured on an Apple M4 Pro (64 GB, macOS 26):
1.38x to 1.89x faster than Accelerate's GEMM at n = 6912 to 13824 under the default budget,
with less error than the GEMM itself (every error is measured against the exact product).

The report: `doc/matmul_mixed_levels.tex` (PDF beside it), "Mixed fast matrix multiplication:
fused levels of accurate square and rectangular schemes over a vendor GEMM, chosen by a
calibrated planner".  The accuracy study of the 4x4 level's programs:
`doc/matmul_4x4_rank48_accurate262.tex`.  The running log of the track since 2026-10-24:
`doc/fastmm_plan.md`.

## The idea

A scheme <g1 x g2 x g3 : r> cuts A, B and C into grids of blocks and is three linear programs
(PLinOpt .slp files): L maps the blocks of A to r left factors, R maps the blocks of B to r
right factors, P maps the r products to the blocks of C.  The library runs one level as three
fused passes: the L pass reads every block of A once and writes the r left factors, the R pass
does the same for B, the r products are GEMM calls or deeper levels, and the P pass reads the r
product blocks once and writes the blocks of C.  The scheme's program is evaluated per element
position in registers, so a pass costs its memory traffic and not its operation count: a 4x4
level moves 12 n^2 words whatever its program, against about 38 n^2 for the 201 linear operations
of our shortest program run one block operation at a time.  The 201-, 262-, 284- and
315-operation programs of the rank-48 scheme run at the same speed as fused passes; they differ
in accuracy, which is why the library uses the most accurate one.

Levels (a plan names its levels from the top to the leaf, e.g. `D48+4/D48/G6`):

- `D48`: the <4x4x4:48> scheme of Dumas, Pernet and Sedoglavic (arXiv:2506.13242) with their
  262-operation accurate program (PLinOpt's `4x4x4_48_accurate_262`); `gen_kernels.py --dps48
  PREFIX` builds the kernels from any other program of the class: `../dps48/cand48/p005_201n`
  (our 201-operation program), PLinOpt's `4x4x4_48_accurate` (284) or `4x4x4_48_rational` (the
  original, 315).
- `R336`, `R363`, `R633`: their accurate <3x3x6:40> scheme in its three orientations,
  rectangular levels whose products are rectangular sub-problems (the three in turn return to
  square blocks); `T336`, `T363`, `T633`: a ternary <3x3x6:42> scheme, a trial.
- `SW`: a <2x2x2:7> level at DPS's most accurate point, in Q(sqrt 3) (`schemes/sw/q3_*`, written
  and checked by `sw_points.py`; their dyadic point with `gen_kernels.py --sw schemes/opt/dps7`,
  Strassen-Winograd's programs with `--sw winograd`); `SW2`: its Kronecker square,
  one <4x4x4:49> level.
- `G`: the leaf, Accelerate's GEMM; `Gk` runs the products in k single-threaded streams; `B2`,
  `B4`, `B8`: classical blocked GEMMs.  A level's `+p` suffix sets the pass threads of its
  pipelined execution.

The planner prices a plan as r times its sub-plan plus the words its passes move over the
measured bandwidth, from a calibration measured once per machine and precision (cached in
`~/Library/Caches/fmm/calib5_f32.txt` and `calib5_f64.txt`, or under `FMM_CALIB_DIR`).  Its error
model knows the order of the levels: the leaf GEMM's error multiplied by every level's
amplification ratio (from the scheme), plus each level's own rounding multiplied by the levels above
it, with three kinds of constants fitted at calibration to the errors of the levels alone and in
ordered pairs against the exact product (fmm.c, "the accuracy budget"; a cache from before
2026-11-23 lacks those entries and plans the classical GEMM until `fmm_calibrate` adds them), and the budget `max_growth` (default 1: no less accurate than the GEMM) bounds the
predicted error.  Without a calibration covering a shape the classical GEMM runs, so results are
always correct.

## Build and run

Requirements: macOS on Apple silicon (compiled with `-mcpu=apple-m4`; change the flag in the
Makefile for another chip), clang and the Accelerate framework; Python 3 with numpy for the
generator and the analysis scripts; a clone of PLinOpt (https://github.com/jgdumas/plinopt) at
`matmul/dps48/plinopt`, whose `data/` directory holds the programs of the 4x4 level.

    make                                      # build/bench_fmm, build/libfmm.a, build/test_fmm, the probes
    build/bench_fmm -n 8192 -t f -r 5 -m classical,dps48,plan=D48+4/D48/G6,auto
    build/bench_fmm -n 13824 -t d -p          # the planner's table for n
    FMM_CALIB_DIR=results build/test_fmm      # the library's entry points against Accelerate

`bench_fmm` options: `-n` (square size) or `-M -K -N` (an m x k by k x n problem), `-t f|d`
(precision), `-r` (interleaved rounds), `-m` (methods, comma-separated: `classical`, `blk2`,
`blk4`, `blk8`, `sw1`, `sw2rec`, `sw3rec`, `sw2`, `dps48`, `dps48ops` for the 201 operations one
block operation at a time, `r336`, `plan=...`, `auto`, `auto:g` for a budget of g, `auto:none`;
the header of `bench_fmm.c` describes them).  `FMM_EXACT=1` measures errors against the exact
product (reference products cached under `FMM_REFCACHE`), `FMM_F64PASS=1` accumulates the f32
passes in f64, `FMM_RECALIB=1` remeasures the calibration, `FMM_MAX_GROWTH=g` changes the default
budget; `FMM_PASS_THREADS`, `FMM_NEON_THREADS`, `FMM_PAD`, `FMM_SEED` and `FMM_NORMAL` are
documented where they are read, in `fmm.c` and `bench_impl.h`.

## The library

`fmm.h`: `fmm_sgemm` and `fmm_dgemm` (n x n), `fmm_sgemm_mkn` and `fmm_dgemm_mkn` (m x k by
k x n), `fmm_calibrate`, `fmm_calibrate_mkn`, `fmm_plan`, `fmm_plan_mkn`, `fmm_release`; link
`build/libfmm.a -framework Accelerate`.  The Rust crate in `rust/` has the same entry points
(`fmm::sgemm`, `fmm::dgemm`, ...), the same plans and the same results bit for bit, and its own
README.  The C library is built with `-ffp-contract=off`, so the passes compute their programs as
written, as Rust does: with clang's default contraction the R336 level's P program, whose one
statement `v + X*5` has a non-dyadic factor, rounded once where Rust rounds twice, and plans with
an R336 level differed from Rust's in the last bits (found 2026-11-16, when the crosscheck first
ran on the real cache at 6912 and 13824).

The planner takes the fastest plan within the error budget and, of the plans predicted within 3%
of it, one predicted at least 10% more accurate, the error model's resolution (faster first,
more accurate second; C and Rust alike).  The passes claim their
output lines with `DC ZVA` before writing them (`FMM_ZVA=0` to switch it off): a store to a line
that is not in the cache first reads it from memory, so a pass that writes 48 blocks and reads 16
moved 112 blocks; claimed, its bandwidth rises from 123 to 168 GB/s (`probe_strip.c`), which is
worth 2-4% on the f32 plans and 0.3% in f64, with the same results (C and Rust alike; in
Rust the asm! for DC ZVA and DCZID_EL0 is in `rust/src/sys.rs`).

## With the GPU (single precision)

`make build/libfmm_gpu.a build/bench_fmm_gpu build/test_fmm_gpu`; link `build/libfmm_gpu.a
-framework Accelerate -framework Foundation -framework Metal -framework MetalPerformanceShaders`.
Metal Performance Shaders' f32 matrix product is bit for bit Accelerate's sgemm (both are the
k-ordered chain of fused multiply-adds), and on unified memory it reads and writes the library's
scratch blocks where they are (`gpu_leaf.m`).  So a level's products can be shared: the GEMM takes
them from one end and the GPU from the other (leaves `GM`: Accelerate's own threading and the
GPU; `G6M`: six streams and the GPU), 7-9 TFLOP/s together against 3.3-3.8.  The planner uses
these leaves on products of 576 and up, and without any level the classical product in strips of
rows (`K16`, `K32`, `K64`: in place, the GEMM's own result; needs page-aligned matrices).  A GPU
plan is held to the predicted error of the fastest plan without the GPU, so it never costs
accuracy; with a leaf this fast the best plans have fewer levels, and at 6912 the error falls.
Measured 2026-11-14 (`results/zva_gpu_campaign_2026-11-14.txt`, exact errors):

| n | without the GPU | with it | GPU alone | Accelerate |
|---|---|---|---|---|
| 3456 | `R363/G6` 0.0202 s, err 1.28e-6 | `R363/G6M` 0.012-0.014 s, the same result | 0.013 s | 0.0245 s |
| 6912 | `R363+4/R633/G6` 0.136 s, 2.20e-6 | `R363/G6M` 0.068-0.084 s, 1.76e-6 | 0.109 s | 0.195 s |
| 13824 | `R363+4/R363/G6` 0.906 s, 2.46e-6 | `R363/G6M` 0.53 s, 2.73e-6 | 0.83 s | 1.55 s |

(The planner's picks.  At 13824 the pick before these changes was `R336+2/R363/G6`, 0.925 s with
error 3.34e-6; the two-level `R336+4/R363/G6M` runs 0.49-0.54 s with that error.)  The ranges are
the same plan at different places in a run: a plan with the GPU runs 10-20% slower right after
CPU-only work than after another GPU plan (not the GPU's clock: keeping it busy during the first
passes changed nothing), which is why the planner treats GPU plans predicted within 8% as ties
and takes the more accurate.  There is no f64 on Metal: double precision is unchanged.
The Rust crate has the same leaves with `--features gpu` (same plans, predictions and results,
bit for bit: `results/crosscheck_2026-11-16.txt`).  `FMM_GPU=0` plans without the GPU; its
calibration entries live beside the cache in `calib5gpu_f32.txt`.

## Files

- `fmm.c`, `fmm_impl.h`, `fmm.h`: the library (planner, executor, calibration, pipelined
  passes); `neon_gemm.h`: a NEON GEMM used beside the SME streams.
- `gen_kernels.py`: the kernel generator (`build/kernels.h`; `--rust` for the crate) from the
  schemes' .slp programs; `schemes/`: the programs of the 2x2 and 3x3x6 levels (`opt/`:
  PLinOpt-optimized, the default).
- `bench_fmm.c`, `bench_impl.h`: the benchmark driver; `test_fmm.c`: the library's entry points
  against Accelerate.
- `run_*.sh`, `campaign_*.sh`: the measurement campaigns; `results/`: their logs, dated; the
  report's tables come from them.
- `altsim.py`: f32 rounding of ordinary and alternative-basis rank-48 programs by block-level
  interpretation; `growth.py`: the growth factors gamma_{p,q} of a scheme; `paper_acc262.py`:
  the accuracy paper's tables and figures; `summarize_var.py`: summaries of the variant campaigns.
- `gpu_gemm.m`: Apple's GPU as a GEMM (MPSGraph), for comparison; `gpu_leaf.h`, `gpu_leaf.m`: the
  GPU as a second engine for a level's products; `gpu_share.m`: its probe; `probe_threads.c`,
  `probe_overlap.c`, `neon_test.c`: machine probes; `probe_nt.c`, `probe_strip.c`: what the passes
  cost the memory system (non-temporal stores, strip-mining, DC ZVA); `sme_gemm.h`, `sme_test.c`:
  our own SME (FMOPA) kernel against Accelerate, a probe.
- `rust/`: the Rust crate, with its README.

## Numbers quoted elsewhere

The paper "Fast matrix multiplication via recursive <4x4x4:48> algorithms into practice"
(Dumas, Patel, Pernet, Sedoglavic, Sidebottom, Stapleton, Tichavsky) quotes this directory at
commit 19fb30e: the same-speed measurement of the 201-, 315- and 284-operation programs
(`results/orig315_2026-10-25.txt`), the one- and two-level times with the 262-operation programs
(the report's results table, `run_budget.sh` and `run_auto.sh`), and the f32 error multiples
(`results/accuracy_campaign_2026-10-25.txt`, `results/altbasis_sim_2026-10-31.txt`).
