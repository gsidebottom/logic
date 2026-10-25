/* fmm.h: fast matrix multiplication on Apple silicon.
 *
 * C = A B for n x n row-major matrices with leading dimensions lda, ldb, ldc (in elements), by
 * the plan a calibrated cost model picks for this machine, size and precision: fused levels of
 * our <4x4x4:48> scheme and of Strassen-Winograd over Accelerate GEMMs, with GEMM streams and
 * pipelined passes.  max_growth > 0 limits the plan's error growth over the classical GEMM's
 * (an estimate, conservative by up to 1.5x; 0: the fastest plan).
 *
 * The plans come from the calibration cache (FMM_CALIB_DIR, default ~/Library/Caches/fmm, one
 * file per precision, keyed by machine).  Where it does not cover n (no calibration yet, or n
 * not a power-of-two multiple of the calibrated sizes) the classical GEMM runs, so results are
 * always correct; fmm_calibrate measures what the planner needs, once per machine (minutes).
 * Calls are serialized: each uses the whole machine.  The workspace (up to about 10 n^2
 * elements) is kept between calls until fmm_release.
 *
 * Link: libfmm.a -framework Accelerate.
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

/* measure the calibration the planner needs for sizes up to n in one precision (f64: 0 or 1)
 * and add it to the cache; returns the number of entries measured */
int fmm_calibrate(size_t n, int f64);

/* the plan fmm_sgemm (f64 = 0) or fmm_dgemm (f64 = 1) runs for n, e.g. "D48+3/D48/G6" ("G": the
 * classical GEMM), and its predicted time in seconds (-1 if not calibrated) */
const char *fmm_plan(size_t n, int f64, double max_growth, double *predicted);

/* free the workspace and the cached calibration and plans */
void fmm_release(void);

#ifdef __cplusplus
}
#endif

#endif
