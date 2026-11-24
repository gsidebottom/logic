/* fmm.h: fast matrix multiplication on Apple silicon.
 *
 * C = A B for n x n row-major matrices with leading dimensions lda, ldb, ldc (in elements), by
 * the plan a calibrated cost model picks for this machine, size and precision: fused levels of
 * the rank-48 <4x4x4:48> scheme of Dumas, Pernet and Sedoglavic (their 262-operation accurate
 * program, PLinOpt's 4x4x4_48_accurate_262), of their accurate <3x3x6:40> scheme in its three
 * orientations (R336, R363, R633: rectangular levels whose products are rectangular sub-problems,
 * so a plan tracks the shape (m x k)(k x n) of each level's products; the three orientations in
 * turn return to square blocks, dividing n by 54) and of a <2x2x2:7> level (SW: DPS's most
 * accurate point, in Q(sqrt 3), Eq. (36) of their ISSAC 2024 paper; their dyadic point with
 * gen_kernels.py --sw schemes/opt/dps7, Strassen-Winograd's programs with --sw winograd), over Accelerate GEMMs, with GEMM streams and pipelined passes.
 * max_growth is the error budget: the plan's predicted error over the classical GEMM's on the
 * same problem, from per-level factors measured against the exact product at calibration (an
 * estimate, good to about 25%).  0 means the default budget of 1, a plan predicted no less
 * accurate than the GEMM it replaces (the accurate levels are more accurate, so the fast plans
 * qualify, and so do the plans with a 2x2 level on top, the fastest in deep f64, since the level's
 * programs are at an accurate point of DPS's: measured at 0.6-1.0 of the GEMM's error, where
 * Strassen-Winograd's programs needed a budget of 2); a positive value is that budget; a negative value means no budget,
 * the fastest plan whatever its error.
 *
 * The plans come from the calibration cache (FMM_CALIB_DIR, default ~/Library/Caches/fmm, one
 * file per precision, calib5_f32.txt and calib5_f64.txt, keyed by machine and kernels); square
 * sizes between the calibrated ones are interpolated, rectangular shapes that were not calibrated
 * are priced from the square measurements (GEMMs by their flops, passes by their traffic: an
 * estimate, which fmm_calibrate_mkn replaces by measurements), and a plan runs padded to the next
 * shape its levels divide when that pays (every dimension to a multiple of 2^a 3^b).
 * FMM_F64PASS=1 makes the 4x4 scheme's passes of the single-precision path add in double
 * (float blocks in and out): the passes then round once per element stored, at the GEMM's
 * interface, instead of at every addition; same plans, same speed, less error at depth.
 * Outside the calibrated range, or without a calibration, the classical GEMM runs, so results
 * are always correct; fmm_calibrate measures what the planner needs, once per machine
 * (minutes).  Calls are serialized: each uses the whole machine.  The workspace (up to about
 * 10 n^2 elements) is kept between calls until fmm_release.
 *
 * Faster first, more accurate second: of the plans predicted within 3% of the fastest within the
 * budget (8% with the GPU, whose timings repeat less well), the planner takes one predicted at
 * least 25% more accurate, the error model's resolution.
 *
 * The passes claim their output lines with DC ZVA before writing them, so that a store does not
 * first fetch from memory a line it is about to overwrite (FMM_ZVA=0 switches it off; the results
 * are the same either way).
 *
 * With the GPU (libfmm_gpu.a, single precision only: Metal has no f64).  Metal Performance
 * Shaders' f32 matrix product is the same k-ordered chain of fused multiply-adds as Accelerate's
 * sgemm, bit for bit, and on unified memory it reads and writes the library's scratch blocks where
 * they are.  A level's products are then shared: the GEMM (Accelerate's own threading, leaf GM, or
 * six streams, G6M) takes them from one end and the GPU from the other, at 7-9 TFLOP/s together
 * against 3.3-3.8 for the streams.  The planner uses these leaves on products whose smallest
 * dimension is at least 576, and, with no level at all, the classical product cut into 16, 32 or
 * 64 strips of rows (K16, K32, K64: in place, the GEMM's own result), which needs page-aligned
 * matrices (16384) to be wrapped for the GPU and a calibration for that very shape; otherwise the
 * best plan without a K level runs.  A plan with the GPU is held to the predicted error of the
 * fastest plan the same budget admits without it, so the GPU never costs accuracy; with a faster
 * leaf the fastest plans have fewer levels, and their error is the same or lower.  The GPU's entries of the
 * calibration live beside the cache in calib5gpu_f32.txt; FMM_GPU=0 plans without the GPU.
 *
 * Link: libfmm.a -framework Accelerate, or libfmm_gpu.a -framework Accelerate -framework Foundation
 * -framework Metal -framework MetalPerformanceShaders.
 */
#ifndef FMM_H
#define FMM_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* C = A B; 0 on success, -1 if the workspace cannot be allocated */
int fmm_sgemm(size_t n, const float *A, size_t lda, const float *B, size_t ldb, float *C, size_t ldc,
              double max_growth);
int fmm_dgemm(size_t n, const double *A, size_t lda, const double *B, size_t ldb, double *C, size_t ldc,
              double max_growth);

/* the same for an m x k matrix A and a k x n matrix B (C is m x n): a rectangular problem; its
 * levels divide m, k and n by their grids; the planner prices its shapes from the square
 * calibration (an estimate) unless they were calibrated (fmm_calibrate_mkn) */
int fmm_sgemm_mkn(size_t m, size_t k, size_t n, const float *A, size_t lda, const float *B, size_t ldb, float *C,
                  size_t ldc, double max_growth);
int fmm_dgemm_mkn(size_t m, size_t k, size_t n, const double *A, size_t lda, const double *B, size_t ldb, double *C,
                  size_t ldc, double max_growth);

/* measure the calibration the planner needs for sizes up to n (square) or for the shape (m, k, n)
 * in one precision (f64: 0 or 1) and add it to the cache; returns the number of entries measured */
int fmm_calibrate(size_t n, int f64);
int fmm_calibrate_mkn(size_t m, size_t k, size_t n, int f64);

/* the plan fmm_sgemm (f64 = 0) or fmm_dgemm (f64 = 1) runs for n, e.g. "D48+3/D48/G6" ("G": the
 * classical GEMM), and its predicted time in seconds (-1 if not calibrated); fmm_plan_mkn the same
 * for a rectangular problem */
const char *fmm_plan(size_t n, int f64, double max_growth, double *predicted);
const char *fmm_plan_mkn(size_t m, size_t k, size_t n, int f64, double max_growth, double *predicted);

/* free the workspace and the cached calibration and plans */
void fmm_release(void);

#ifdef __cplusplus
}
#endif

#endif
