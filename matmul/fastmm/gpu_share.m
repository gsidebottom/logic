/* gpu_share: the products of a fused level shared between the GPU and the SME units.
 * r products of shape (m x k)(k x n), f32, their operands and results blocks of three page-aligned
 * arrays wrapped as shared Metal buffers without a copy (unified memory), as the library's scratch
 * would be.  Three timings, caches evicted before each:
 *   cpu   t single-threaded Accelerate streams taking products in turn (the library's Gk leaf)
 *   gpu   the GPU alone: MPSMatrixMultiplication, up to d products per command buffer, one submitter
 *   both  the streams take products from the front, the GPU from the back, until they meet
 * and the largest difference between the GPU's and Accelerate's results (0: bit-identical).
 *   usage: gpu_share m k n [r] [streams] [depth]
 * Build: see Makefile (build/gpu_share). */
#import <Foundation/Foundation.h>
#import <Metal/Metal.h>
#import <MetalPerformanceShaders/MetalPerformanceShaders.h>
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <dispatch/dispatch.h>
#include <math.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC_RAW, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static void evict(void) {
    static unsigned char *buf;
    static unsigned char val;
    size_t len = (size_t)128 << 20, chunks = 64, step = len / chunks;
    if (!buf) posix_memalign((void **)&buf, 16384, len);
    val++;
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
        memset(buf + ch * step, val, step);
    });
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: gpu_share m k n [r] [streams] [depth]\n"); return 1; }
    size_t m = strtoull(argv[1], NULL, 10), k = strtoull(argv[2], NULL, 10), n = strtoull(argv[3], NULL, 10);
    int r = argc > 4 ? atoi(argv[4]) : 40, streams = argc > 5 ? atoi(argv[5]) : 6, depth = argc > 6 ? atoi(argv[6]) : 2;
    @autoreleasepool {
        id<MTLDevice> dev = MTLCreateSystemDefaultDevice();
        if (!dev) { fprintf(stderr, "no Metal device\n"); return 1; }
        size_t page = 16384, sa = m * k, sb = k * n, sc = m * n;
        size_t ba = (((size_t)r * sa * 4 + page - 1) / page) * page, bb = (((size_t)r * sb * 4 + page - 1) / page) * page,
               bc = (((size_t)r * sc * 4 + page - 1) / page) * page;
        float *A, *B, *C, *D;
        if (posix_memalign((void **)&A, page, ba) || posix_memalign((void **)&B, page, bb) ||
            posix_memalign((void **)&C, page, bc) || posix_memalign((void **)&D, page, bc)) { fprintf(stderr, "alloc\n"); return 1; }
        uint64_t s = 0x9e3779b97f4a7c15ull;
        for (size_t i = 0; i < (size_t)r * sa; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; A[i] = (float)((double)(s >> 11) / 9007199254740992.0 * 2 - 1); }
        for (size_t i = 0; i < (size_t)r * sb; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; B[i] = (float)((double)(s >> 11) / 9007199254740992.0 * 2 - 1); }
        memset(C, 0, bc);
        memset(D, 0, bc);
        id<MTLBuffer> mA = [dev newBufferWithBytesNoCopy:A length:ba options:MTLResourceStorageModeShared deallocator:nil];
        id<MTLBuffer> mB = [dev newBufferWithBytesNoCopy:B length:bb options:MTLResourceStorageModeShared deallocator:nil];
        id<MTLBuffer> mC = [dev newBufferWithBytesNoCopy:C length:bc options:MTLResourceStorageModeShared deallocator:nil];
        if (!mA || !mB || !mC) { fprintf(stderr, "buffer wrap failed\n"); return 1; }
        MPSMatrixDescriptor *dA = [MPSMatrixDescriptor matrixDescriptorWithRows:m columns:k rowBytes:k * 4 dataType:MPSDataTypeFloat32];
        MPSMatrixDescriptor *dB = [MPSMatrixDescriptor matrixDescriptorWithRows:k columns:n rowBytes:n * 4 dataType:MPSDataTypeFloat32];
        MPSMatrixDescriptor *dC = [MPSMatrixDescriptor matrixDescriptorWithRows:m columns:n rowBytes:n * 4 dataType:MPSDataTypeFloat32];
        NSMutableArray<MPSMatrix *> *xa = [NSMutableArray new], *xb = [NSMutableArray new], *xc = [NSMutableArray new];
        for (int q = 0; q < r; q++) {
            [xa addObject:[[MPSMatrix alloc] initWithBuffer:mA offset:(size_t)q * sa * 4 descriptor:dA]];
            [xb addObject:[[MPSMatrix alloc] initWithBuffer:mB offset:(size_t)q * sb * 4 descriptor:dB]];
            [xc addObject:[[MPSMatrix alloc] initWithBuffer:mC offset:(size_t)q * sc * 4 descriptor:dC]];
        }
        MPSMatrixMultiplication *mm = [[MPSMatrixMultiplication alloc] initWithDevice:dev transposeLeft:NO transposeRight:NO
                                                                           resultRows:m resultColumns:n interiorColumns:k
                                                                                alpha:1.0 beta:0.0];
        id<MTLCommandQueue> cq = [dev newCommandQueue];
        dispatch_queue_t gq = dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0);
        double flop = 2.0 * m * k * n * r;
        /* mode 0 cpu, 1 gpu, 2 both; the cpu's results go to D in mode 0 (the reference), to C otherwise */
        double best[3] = {1e9, 1e9, 1e9};
        int gshare[3] = {0, 0, 0};
        for (int rep = -1; rep < 3; rep++)
            for (int mode = 0; mode < 3; mode++) {
                atomic_int lo = 0, hi = r - 1, gdone = 0;
                atomic_int *plo = &lo, *phi = &hi, *pgd = &gdone;
                /* a product index for the streams (from the front) or the GPU (from the back); -1: none left */
                int (^take)(int) = ^(int front) {
                    for (;;) {
                        int l = atomic_load(plo), h = atomic_load(phi);
                        if (l > h) return -1;
                        if (front) { if (atomic_compare_exchange_weak(plo, &l, l + 1)) return l; }
                        else if (atomic_compare_exchange_weak(phi, &h, h - 1)) return h;
                    }
                };
                float *Out = mode == 0 ? D : C;
                evict();
                double t0 = now();
                dispatch_group_t grp = dispatch_group_create();
                if (mode != 1)
                    for (int w = 0; w < streams; w++)
                        dispatch_group_async(grp, gq, ^{
                            enum BLAS_THREADING old = BLASGetThreading();
                            BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
                            for (int q; (q = take(1)) >= 0;)
                                cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)m, (int)n, (int)k, 1.0f, A + (size_t)q * sa,
                                            (int)k, B + (size_t)q * sb, (int)n, 0.0f, Out + (size_t)q * sc, (int)n);
                            BLASSetThreading(old);
                        });
                if (mode != 0)      /* one submitter: up to `depth` products per command buffer */
                    dispatch_group_async(grp, gq, ^{
                        for (;;) {
                            @autoreleasepool {
                                id<MTLCommandBuffer> cb = [cq commandBuffer];
                                int cnt = 0;
                                for (int q; cnt < depth && (q = take(0)) >= 0; cnt++)
                                    [mm encodeToCommandBuffer:cb leftMatrix:xa[q] rightMatrix:xb[q] resultMatrix:xc[q]];
                                if (!cnt) break;
                                [cb commit];
                                [cb waitUntilCompleted];
                                atomic_fetch_add(pgd, cnt);
                            }
                        }
                    });
                dispatch_group_wait(grp, DISPATCH_TIME_FOREVER);
                double t = now() - t0;
                if (rep >= 0 && t < best[mode]) { best[mode] = t; gshare[mode] = atomic_load(pgd); }
            }
        double diff = 0, mx = 0;
        for (size_t i = 0; i < (size_t)r * sc; i++) {
            diff = fmax(diff, fabs((double)C[i] - (double)D[i]));
            mx = fmax(mx, fabs((double)D[i]));
        }
        printf("gpu_share %5zux%5zux%5zu r=%3d streams=%d depth=%d  cpu %7.4f s %7.1f GF  gpu %7.4f s %7.1f GF  both %7.4f s %7.1f GF"
               " (gpu took %d)  both/cpu %.2fx  maxdiff/max %.1e\n",
               m, k, n, r, streams, depth, best[0], flop / best[0] / 1e9, best[1], flop / best[1] / 1e9, best[2], flop / best[2] / 1e9,
               gshare[2], best[0] / best[2], diff / mx);
        fflush(stdout);
    }
    return 0;
}
