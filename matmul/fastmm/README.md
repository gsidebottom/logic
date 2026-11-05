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
- `SW`: a <2x2x2:7> level with DPS's dyadic accurate point (`schemes/opt/dps7_*`;
  Strassen-Winograd's programs with `gen_kernels.py --sw winograd`); `SW2`: its Kronecker square,
  one <4x4x4:49> level.
- `G`: the leaf, Accelerate's GEMM; `Gk` runs the products in k single-threaded streams; `B2`,
  `B4`, `B8`: classical blocked GEMMs.  A level's `+p` suffix sets the pass threads of its
  pipelined execution.

The planner prices a plan as r times its sub-plan plus the words its passes move over the
measured bandwidth, from a calibration measured once per machine and precision (cached in
`~/Library/Caches/fmm/calib5_f32.txt` and `calib5_f64.txt`, or under `FMM_CALIB_DIR`).  Its error
model has one factor per level and a depth factor, measured against the exact product at
calibration, and the budget `max_growth` (default 1: no less accurate than the GEMM) bounds the
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
README.

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
- `gpu_gemm.m`: Apple's GPU as a GEMM (MPSGraph), for comparison; `probe_threads.c`,
  `probe_overlap.c`, `neon_test.c`: machine probes.
- `rust/`: the Rust crate, with its README.

## Numbers quoted elsewhere

The paper "Fast matrix multiplication via recursive <4x4x4:48> algorithms into practice"
(Dumas, Patel, Pernet, Sedoglavic, Sidebottom, Stapleton, Tichavsky) quotes this directory at
commit 19fb30e: the same-speed measurement of the 201-, 315- and 284-operation programs
(`results/orig315_2026-10-25.txt`), the one- and two-level times with the 262-operation programs
(the report's results table, `run_budget.sh` and `run_auto.sh`), and the f32 error multiples
(`results/accuracy_campaign_2026-10-25.txt`, `results/altbasis_sim_2026-10-31.txt`).
