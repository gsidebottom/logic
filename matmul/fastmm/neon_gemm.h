/* neon_gemm.h: GEMM on the NEON vector units of one core, for the cores Accelerate's SME GEMM
 * leaves idle.  neon_sgemm_rows / neon_dgemm_rows compute rows r0..r1 of C = A B (n x n,
 * row-major, leading dimensions lda, ldb, ldc), so several cores can share one product.
 *
 * GotoBLAS structure: for each KC-deep slice of the inner dimension, pack the slice of B into
 * NR-wide panels and the rows' slice of A into MR-tall panels (both contiguous in the order the
 * micro-kernel reads them), then run the micro-kernel on every MR x NR tile: MR x NR
 * accumulators in registers, per step of k one load of MR values of A, one of NR values of B and
 * MR * NR / lanes fused multiply-adds by lane.  f32: 8 x 8 tile (16 accumulators); f64: 4 x 8
 * (16 accumulators).  n must be a multiple of 8 and r0, r1 multiples of MR.
 *
 * Loop order: for each MC-row block of A (kept in L1: 64 KB) all of the packed B slice streams
 * from L2 once, so B is read from L2 (r1 - r0) / MC times per slice; streaming all of A's rows
 * for each 8-column panel of B instead reads 8x more from L2 and starves the SME units, which
 * share the cluster's L2 (neon_test).
 *
 * The caller provides the packing buffers: pa holds (r1 - r0) * KC elements, pb holds KC * n. */
#include <arm_neon.h>
#include <stddef.h>
#include <string.h>

#define NEON_KC 256
#define NEON_MC_S 64    /* f32 rows per L1 block: 64 x 256 x 4 B = 64 KB */
#define NEON_MC_D 32    /* f64: 32 x 256 x 8 B = 64 KB */

/* ---- f32: 8 x 8 tiles ------------------------------------------------------------------ */
static void neon_s_kernel(size_t kc, const float *restrict a, const float *restrict b, float *restrict c,
                          size_t ldc, int accumulate) {
    float32x4_t c00 = vdupq_n_f32(0), c01 = c00, c10 = c00, c11 = c00, c20 = c00, c21 = c00, c30 = c00,
                c31 = c00, c40 = c00, c41 = c00, c50 = c00, c51 = c00, c60 = c00, c61 = c00, c70 = c00,
                c71 = c00;
    for (size_t k = 0; k < kc; k++) {
        float32x4_t a0 = vld1q_f32(a), a1 = vld1q_f32(a + 4), b0 = vld1q_f32(b), b1 = vld1q_f32(b + 4);
        c00 = vfmaq_laneq_f32(c00, b0, a0, 0); c01 = vfmaq_laneq_f32(c01, b1, a0, 0);
        c10 = vfmaq_laneq_f32(c10, b0, a0, 1); c11 = vfmaq_laneq_f32(c11, b1, a0, 1);
        c20 = vfmaq_laneq_f32(c20, b0, a0, 2); c21 = vfmaq_laneq_f32(c21, b1, a0, 2);
        c30 = vfmaq_laneq_f32(c30, b0, a0, 3); c31 = vfmaq_laneq_f32(c31, b1, a0, 3);
        c40 = vfmaq_laneq_f32(c40, b0, a1, 0); c41 = vfmaq_laneq_f32(c41, b1, a1, 0);
        c50 = vfmaq_laneq_f32(c50, b0, a1, 1); c51 = vfmaq_laneq_f32(c51, b1, a1, 1);
        c60 = vfmaq_laneq_f32(c60, b0, a1, 2); c61 = vfmaq_laneq_f32(c61, b1, a1, 2);
        c70 = vfmaq_laneq_f32(c70, b0, a1, 3); c71 = vfmaq_laneq_f32(c71, b1, a1, 3);
        a += 8;
        b += 8;
    }
    float32x4_t acc[8][2] = {{c00, c01}, {c10, c11}, {c20, c21}, {c30, c31},
                             {c40, c41}, {c50, c51}, {c60, c61}, {c70, c71}};
    for (int i = 0; i < 8; i++) {
        float *row = c + i * ldc;
        if (accumulate) {
            acc[i][0] = vaddq_f32(acc[i][0], vld1q_f32(row));
            acc[i][1] = vaddq_f32(acc[i][1], vld1q_f32(row + 4));
        }
        vst1q_f32(row, acc[i][0]);
        vst1q_f32(row + 4, acc[i][1]);
    }
}

static void neon_sgemm_rows(size_t n, const float *A, size_t lda, const float *B, size_t ldb, float *C,
                            size_t ldc, size_t r0, size_t r1, float *pa, float *pb) {
    for (size_t p0 = 0; p0 < n; p0 += NEON_KC) {
        size_t kc = n - p0 < NEON_KC ? n - p0 : NEON_KC;
        /* B[p0 : p0 + kc, :] into 8-wide panels: panel j holds kc rows of 8 */
        for (size_t j = 0; j < n; j += 8)
            for (size_t k = 0; k < kc; k++)
                memcpy(pb + j * kc + k * 8, B + (p0 + k) * ldb + j, 8 * sizeof(float));
        /* A[r0 : r1, p0 : p0 + kc] into 8-tall panels, column by column */
        for (size_t i = r0; i < r1; i += 8) {
            float *dst = pa + (i - r0) * kc;
            for (size_t k = 0; k < kc; k++)
                for (int ii = 0; ii < 8; ii++) dst[k * 8 + ii] = A[(i + ii) * lda + p0 + k];
        }
        for (size_t ic = r0; ic < r1; ic += NEON_MC_S) {
            size_t ie = ic + NEON_MC_S < r1 ? ic + NEON_MC_S : r1;
            for (size_t j = 0; j < n; j += 8)
                for (size_t i = ic; i < ie; i += 8)
                    neon_s_kernel(kc, pa + (i - r0) * kc, pb + j * kc, C + i * ldc + j, ldc, p0 > 0);
        }
    }
}

/* ---- f64: 4 x 8 tiles ------------------------------------------------------------------ */
static void neon_d_kernel(size_t kc, const double *restrict a, const double *restrict b, double *restrict c,
                          size_t ldc, int accumulate) {
    float64x2_t c00 = vdupq_n_f64(0), c01 = c00, c02 = c00, c03 = c00, c10 = c00, c11 = c00, c12 = c00,
                c13 = c00, c20 = c00, c21 = c00, c22 = c00, c23 = c00, c30 = c00, c31 = c00, c32 = c00,
                c33 = c00;
    for (size_t k = 0; k < kc; k++) {
        float64x2_t a0 = vld1q_f64(a), a1 = vld1q_f64(a + 2);
        float64x2_t b0 = vld1q_f64(b), b1 = vld1q_f64(b + 2), b2 = vld1q_f64(b + 4), b3 = vld1q_f64(b + 6);
        c00 = vfmaq_laneq_f64(c00, b0, a0, 0); c01 = vfmaq_laneq_f64(c01, b1, a0, 0);
        c02 = vfmaq_laneq_f64(c02, b2, a0, 0); c03 = vfmaq_laneq_f64(c03, b3, a0, 0);
        c10 = vfmaq_laneq_f64(c10, b0, a0, 1); c11 = vfmaq_laneq_f64(c11, b1, a0, 1);
        c12 = vfmaq_laneq_f64(c12, b2, a0, 1); c13 = vfmaq_laneq_f64(c13, b3, a0, 1);
        c20 = vfmaq_laneq_f64(c20, b0, a1, 0); c21 = vfmaq_laneq_f64(c21, b1, a1, 0);
        c22 = vfmaq_laneq_f64(c22, b2, a1, 0); c23 = vfmaq_laneq_f64(c23, b3, a1, 0);
        c30 = vfmaq_laneq_f64(c30, b0, a1, 1); c31 = vfmaq_laneq_f64(c31, b1, a1, 1);
        c32 = vfmaq_laneq_f64(c32, b2, a1, 1); c33 = vfmaq_laneq_f64(c33, b3, a1, 1);
        a += 4;
        b += 8;
    }
    float64x2_t acc[4][4] = {{c00, c01, c02, c03}, {c10, c11, c12, c13}, {c20, c21, c22, c23},
                             {c30, c31, c32, c33}};
    for (int i = 0; i < 4; i++) {
        double *row = c + i * ldc;
        for (int q = 0; q < 4; q++) {
            if (accumulate) acc[i][q] = vaddq_f64(acc[i][q], vld1q_f64(row + 2 * q));
            vst1q_f64(row + 2 * q, acc[i][q]);
        }
    }
}

static void neon_dgemm_rows(size_t n, const double *A, size_t lda, const double *B, size_t ldb, double *C,
                            size_t ldc, size_t r0, size_t r1, double *pa, double *pb) {
    for (size_t p0 = 0; p0 < n; p0 += NEON_KC) {
        size_t kc = n - p0 < NEON_KC ? n - p0 : NEON_KC;
        for (size_t j = 0; j < n; j += 8)
            for (size_t k = 0; k < kc; k++)
                memcpy(pb + j * kc + k * 8, B + (p0 + k) * ldb + j, 8 * sizeof(double));
        for (size_t i = r0; i < r1; i += 4) {
            double *dst = pa + (i - r0) * kc;
            for (size_t k = 0; k < kc; k++)
                for (int ii = 0; ii < 4; ii++) dst[k * 4 + ii] = A[(i + ii) * lda + p0 + k];
        }
        for (size_t ic = r0; ic < r1; ic += NEON_MC_D) {
            size_t ie = ic + NEON_MC_D < r1 ? ic + NEON_MC_D : r1;
            for (size_t j = 0; j < n; j += 8)
                for (size_t i = ic; i < ie; i += 4)
                    neon_d_kernel(kc, pa + (i - r0) * kc, pb + j * kc, C + i * ldc + j, ldc, p0 > 0);
        }
    }
}
