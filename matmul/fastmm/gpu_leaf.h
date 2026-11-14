/* gpu_leaf.h: the GPU as a second engine for the products of a fused level (f32 only; Metal
 * Performance Shaders' matrix multiplication on shared, uncopied memory).  The caller attaches the
 * page-aligned regions its operands and results live in; a batch of products given by pointers
 * into attached regions is encoded in one command buffer and waited for.  The GPU's f32 product
 * is the k-ordered chain of fused multiply-adds, bit for bit Accelerate's sgemm (gpu_gemm.m,
 * gpu_share.m), so sharing a level's products with it leaves a plan's result unchanged. */
#ifndef GPU_LEAF_H
#define GPU_LEAF_H
#include <stddef.h>

/* wrap [base, base + bytes) as a shared Metal buffer (no copy); base must be page-aligned (16384)
 * and the allocation must extend to the end of its last page (any page-granular allocation does);
 * 0 on success, -1 if there is no GPU or the region cannot be wrapped */
int fmm_gpu_attach(const void *base, size_t bytes);
void fmm_gpu_detach_all(void);
/* C[i] (m x n, leading dimension ldc) = A[i] (m x k, lda) B[i] (k x n, ldb) for i < count, every
 * block inside an attached region; 0 on success, -1 if a block is not (nothing is computed) */
int fmm_gpu_sgemm_batch(size_t m, size_t k, size_t n, int count, const float *const *A, size_t lda,
                        const float *const *B, size_t ldb, float *const *C, size_t ldc);
#endif
