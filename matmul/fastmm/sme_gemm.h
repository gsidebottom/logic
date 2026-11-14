/* sme_gemm.h: our own GEMM leaf on the SME units (FMOPA outer products), for the products of a
 * fused level.  C (m x n, row-major, ldc) = A B with A given transposed: AT is k x m row-major
 * (ldat), B is k x n row-major (ldb).  Step p of the inner dimension adds the outer product of
 * column p of A (row p of AT, contiguous) and row p of B (contiguous) to a ZA block, so neither
 * operand is packed or copied: the passes that write the operands leave them in the layout the
 * kernel reads.  Each element of C is the k-ordered chain of fused multiply-adds, the same sum in
 * the same order as Accelerate's GEMM (results bit-identical on the sizes tried).
 *
 * f64: vectors of 8, the 8 tiles of ZA.D hold a 16 x 32 block of C (2 vectors of A's column, 4 of
 * B's row, 8 FMOPAs per step); f32: vectors of 16, the 4 tiles of ZA.S hold 32 x 32 (2 x 2).
 * The inner dimension is cut into chunks of SME_KC steps so that the rows a block reads (KC rows
 * of 4 or 6 cache lines) stay in L1 while the block's columns of A change; later chunks load the
 * block of C back into ZA and continue the same chain.  Leading dimensions should be an odd
 * number of cache lines (sme_ld): rows a multiple of a large power of two apart share L1 sets.
 *
 * Needs -mcpu=apple-m4 (SME2 without SVE: the functions enter streaming mode themselves). */
#ifndef SME_GEMM_H
#define SME_GEMM_H
#include <arm_sme.h>
#include <stddef.h>
#include <stdint.h>

#ifndef SME_KC
#define SME_KC 256
#endif

/* a leading dimension of at least n elements of `size` bytes that is an odd number of cache lines */
static inline size_t sme_ld(size_t n, size_t size) {
    size_t per = 64 / size, lines = (n + per - 1) / per;
    if (lines % 2 == 0) lines++;
    return lines * per;
}

__arm_new("za") __arm_locally_streaming
static void sme_dgemm_at(size_t m, size_t k, size_t n, const double *AT, size_t ldat, const double *B, size_t ldb,
                         double *C, size_t ldc) {
    for (size_t pc = 0; pc < k; pc += SME_KC) {
        size_t pe = pc + SME_KC < k ? pc + SME_KC : k;
        for (size_t j0 = 0; j0 < n; j0 += 32) {
            svbool_t q0 = svwhilelt_b64_u64(j0, n), q1 = svwhilelt_b64_u64(j0 + 8, n),
                     q2 = svwhilelt_b64_u64(j0 + 16, n), q3 = svwhilelt_b64_u64(j0 + 24, n);
            for (size_t i0 = 0; i0 < m; i0 += 16) {
                svbool_t p0 = svwhilelt_b64_u64(i0, m), p1 = svwhilelt_b64_u64(i0 + 8, m);
                size_t rows = m - i0 < 16 ? m - i0 : 16;
                if (pc == 0) {
                    svzero_za();
                } else {
                    for (size_t i = 0; i < rows; i++) {
                        const double *c = C + (i0 + i) * ldc + j0;
                        uint32_t s = (uint32_t)(i & 7);
                        if (i < 8) {
                            svld1_hor_za64(0, s, q0, c);
                            svld1_hor_za64(1, s, q1, c + 8);
                            svld1_hor_za64(2, s, q2, c + 16);
                            svld1_hor_za64(3, s, q3, c + 24);
                        } else {
                            svld1_hor_za64(4, s, q0, c);
                            svld1_hor_za64(5, s, q1, c + 8);
                            svld1_hor_za64(6, s, q2, c + 16);
                            svld1_hor_za64(7, s, q3, c + 24);
                        }
                    }
                }
                const double *a = AT + pc * ldat + i0, *b = B + pc * ldb + j0;
                for (size_t p = pc; p < pe; p++, a += ldat, b += ldb) {
                    svfloat64_t x0 = svld1_f64(p0, a), x1 = svld1_f64(p1, a + 8);
                    svfloat64_t y0 = svld1_f64(q0, b), y1 = svld1_f64(q1, b + 8), y2 = svld1_f64(q2, b + 16),
                                y3 = svld1_f64(q3, b + 24);
                    svmopa_za64_f64_m(0, p0, q0, x0, y0);
                    svmopa_za64_f64_m(1, p0, q1, x0, y1);
                    svmopa_za64_f64_m(2, p0, q2, x0, y2);
                    svmopa_za64_f64_m(3, p0, q3, x0, y3);
                    svmopa_za64_f64_m(4, p1, q0, x1, y0);
                    svmopa_za64_f64_m(5, p1, q1, x1, y1);
                    svmopa_za64_f64_m(6, p1, q2, x1, y2);
                    svmopa_za64_f64_m(7, p1, q3, x1, y3);
                }
                for (size_t i = 0; i < rows; i++) {
                    double *c = C + (i0 + i) * ldc + j0;
                    uint32_t s = (uint32_t)(i & 7);
                    if (i < 8) {
                        svst1_hor_za64(0, s, q0, c);
                        svst1_hor_za64(1, s, q1, c + 8);
                        svst1_hor_za64(2, s, q2, c + 16);
                        svst1_hor_za64(3, s, q3, c + 24);
                    } else {
                        svst1_hor_za64(4, s, q0, c);
                        svst1_hor_za64(5, s, q1, c + 8);
                        svst1_hor_za64(6, s, q2, c + 16);
                        svst1_hor_za64(7, s, q3, c + 24);
                    }
                }
            }
        }
    }
}

__arm_new("za") __arm_locally_streaming
static void sme_sgemm_at(size_t m, size_t k, size_t n, const float *AT, size_t ldat, const float *B, size_t ldb,
                         float *C, size_t ldc) {
    for (size_t pc = 0; pc < k; pc += SME_KC) {
        size_t pe = pc + SME_KC < k ? pc + SME_KC : k;
        for (size_t j0 = 0; j0 < n; j0 += 32) {
            svbool_t q0 = svwhilelt_b32_u64(j0, n), q1 = svwhilelt_b32_u64(j0 + 16, n);
            for (size_t i0 = 0; i0 < m; i0 += 32) {
                svbool_t p0 = svwhilelt_b32_u64(i0, m), p1 = svwhilelt_b32_u64(i0 + 16, m);
                size_t rows = m - i0 < 32 ? m - i0 : 32;
                if (pc == 0) {
                    svzero_za();
                } else {
                    for (size_t i = 0; i < rows; i++) {
                        const float *c = C + (i0 + i) * ldc + j0;
                        uint32_t s = (uint32_t)(i & 15);
                        if (i < 16) {
                            svld1_hor_za32(0, s, q0, c);
                            svld1_hor_za32(1, s, q1, c + 16);
                        } else {
                            svld1_hor_za32(2, s, q0, c);
                            svld1_hor_za32(3, s, q1, c + 16);
                        }
                    }
                }
                const float *a = AT + pc * ldat + i0, *b = B + pc * ldb + j0;
                for (size_t p = pc; p < pe; p++, a += ldat, b += ldb) {
                    svfloat32_t x0 = svld1_f32(p0, a), x1 = svld1_f32(p1, a + 16);
                    svfloat32_t y0 = svld1_f32(q0, b), y1 = svld1_f32(q1, b + 16);
                    svmopa_za32_f32_m(0, p0, q0, x0, y0);
                    svmopa_za32_f32_m(1, p0, q1, x0, y1);
                    svmopa_za32_f32_m(2, p1, q0, x1, y0);
                    svmopa_za32_f32_m(3, p1, q1, x1, y1);
                }
                for (size_t i = 0; i < rows; i++) {
                    float *c = C + (i0 + i) * ldc + j0;
                    uint32_t s = (uint32_t)(i & 15);
                    if (i < 16) {
                        svst1_hor_za32(0, s, q0, c);
                        svst1_hor_za32(1, s, q1, c + 16);
                    } else {
                        svst1_hor_za32(2, s, q0, c);
                        svst1_hor_za32(3, s, q1, c + 16);
                    }
                }
            }
        }
    }
}
#endif
