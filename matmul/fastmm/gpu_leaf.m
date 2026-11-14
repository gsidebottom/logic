/* gpu_leaf.m: see gpu_leaf.h.  Build with -fobjc-arc and the Foundation, Metal and
 * MetalPerformanceShaders frameworks. */
#import <Foundation/Foundation.h>
#import <Metal/Metal.h>
#import <MetalPerformanceShaders/MetalPerformanceShaders.h>
#include <pthread.h>
#include <stdint.h>
#include "gpu_leaf.h"

#define NREG 16
#define NKERN 16
static id<MTLDevice> g_dev;
static id<MTLCommandQueue> g_cq;
static id<MTLBuffer> g_buf[NREG];
static const char *g_base[NREG];
static size_t g_len[NREG];
static int g_nreg;
static MPSMatrixMultiplication *g_kern[NKERN];
static size_t g_km[NKERN], g_kk[NKERN], g_kn[NKERN];
static int g_nkern, g_knext;
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;

static int gpu_init(void) {
    if (!g_dev) {
        g_dev = MTLCreateSystemDefaultDevice();
        if (g_dev) g_cq = [g_dev newCommandQueue];
    }
    return g_dev && g_cq ? 0 : -1;
}

int fmm_gpu_attach(const void *base, size_t bytes) {
    const size_t page = 16384;
    int rc = -1;
    pthread_mutex_lock(&g_lock);
    if (gpu_init() == 0 && ((uintptr_t)base % page) == 0 && bytes > 0) {
        size_t len = (bytes + page - 1) / page * page;
        for (int i = 0; i < g_nreg && rc; i++)
            if (g_base[i] == (const char *)base && g_len[i] >= len) rc = 0;
        if (rc && g_nreg < NREG) {
            id<MTLBuffer> b = [g_dev newBufferWithBytesNoCopy:(void *)base length:len options:MTLResourceStorageModeShared deallocator:nil];
            if (b) {
                g_buf[g_nreg] = b;
                g_base[g_nreg] = (const char *)base;
                g_len[g_nreg++] = len;
                rc = 0;
            }
        }
    }
    pthread_mutex_unlock(&g_lock);
    return rc;
}

int fmm_gpu_available(void) {
    pthread_mutex_lock(&g_lock);
    int ok = gpu_init() == 0;
    pthread_mutex_unlock(&g_lock);
    return ok;
}

void fmm_gpu_detach(const void *base) {
    pthread_mutex_lock(&g_lock);
    for (int i = 0; i < g_nreg; i++)
        if (g_base[i] == (const char *)base) {
            g_buf[i] = g_buf[g_nreg - 1];
            g_base[i] = g_base[g_nreg - 1];
            g_len[i] = g_len[g_nreg - 1];
            g_buf[--g_nreg] = nil;
            break;
        }
    pthread_mutex_unlock(&g_lock);
}

void fmm_gpu_detach_all(void) {
    pthread_mutex_lock(&g_lock);
    for (int i = 0; i < g_nreg; i++) g_buf[i] = nil;
    g_nreg = 0;
    pthread_mutex_unlock(&g_lock);
}

/* the attached region holding [p, p + bytes), or -1 */
static int region_of(const void *p, size_t bytes) {
    const char *c = (const char *)p;
    for (int i = 0; i < g_nreg; i++)
        if (c >= g_base[i] && c + bytes <= g_base[i] + g_len[i]) return i;
    return -1;
}

int fmm_gpu_sgemm_batch(size_t m, size_t k, size_t n, int count, const float *const *A, size_t lda,
                        const float *const *B, size_t ldb, float *const *C, size_t ldc) {
    int rc = 0;
    @autoreleasepool {
        pthread_mutex_lock(&g_lock);
        MPSMatrixMultiplication *mm = nil;
        if (gpu_init() != 0) rc = -1;
        for (int i = 0; i < g_nkern && !rc && !mm; i++)
            if (g_km[i] == m && g_kk[i] == k && g_kn[i] == n) mm = g_kern[i];
        if (!rc && !mm) {
            mm = [[MPSMatrixMultiplication alloc] initWithDevice:g_dev transposeLeft:NO transposeRight:NO resultRows:m
                                                   resultColumns:n interiorColumns:k alpha:1.0 beta:0.0];
            int slot = g_nkern < NKERN ? g_nkern++ : (g_knext++ % NKERN);
            g_kern[slot] = mm;
            g_km[slot] = m; g_kk[slot] = k; g_kn[slot] = n;
        }
        id<MTLCommandBuffer> cb = nil;
        if (!rc) {
            MPSMatrixDescriptor *dA = [MPSMatrixDescriptor matrixDescriptorWithRows:m columns:k rowBytes:lda * 4 dataType:MPSDataTypeFloat32];
            MPSMatrixDescriptor *dB = [MPSMatrixDescriptor matrixDescriptorWithRows:k columns:n rowBytes:ldb * 4 dataType:MPSDataTypeFloat32];
            MPSMatrixDescriptor *dC = [MPSMatrixDescriptor matrixDescriptorWithRows:m columns:n rowBytes:ldc * 4 dataType:MPSDataTypeFloat32];
            int ra[64], rb[64], rcx[64];
            if (count > 64) rc = -1;
            for (int i = 0; i < count && !rc; i++) {
                ra[i] = region_of(A[i], m * lda * 4);
                rb[i] = region_of(B[i], k * ldb * 4);
                rcx[i] = region_of(C[i], m * ldc * 4);
                if (ra[i] < 0 || rb[i] < 0 || rcx[i] < 0) rc = -1;
            }
            if (!rc) {
                cb = [g_cq commandBuffer];
                for (int i = 0; i < count; i++) {
                    MPSMatrix *xa = [[MPSMatrix alloc] initWithBuffer:g_buf[ra[i]] offset:(size_t)((const char *)A[i] - g_base[ra[i]]) descriptor:dA];
                    MPSMatrix *xb = [[MPSMatrix alloc] initWithBuffer:g_buf[rb[i]] offset:(size_t)((const char *)B[i] - g_base[rb[i]]) descriptor:dB];
                    MPSMatrix *xc = [[MPSMatrix alloc] initWithBuffer:g_buf[rcx[i]] offset:(size_t)((const char *)C[i] - g_base[rcx[i]]) descriptor:dC];
                    [mm encodeToCommandBuffer:cb leftMatrix:xa rightMatrix:xb resultMatrix:xc];
                }
                [cb commit];
            }
        }
        pthread_mutex_unlock(&g_lock);
        if (cb) {
            [cb waitUntilCompleted];
            if (cb.status != MTLCommandBufferStatusCompleted) rc = -2;
        }
    }
    return rc;
}
