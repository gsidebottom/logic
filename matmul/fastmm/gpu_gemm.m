/* gpu_gemm: the M4 Pro's GPU as a GEMM, for the comparison with the fused-level plans on the CPU.
 * Same inputs as bench_fmm (the xorshift64 stream, uniform [-1,1), seed 0), the matrices wrapped as
 * shared Metal buffers without a copy (unified memory, page-aligned), the product by
 * MPSMatrixMultiplication in f32 (or with f16 inputs and an f32 result: "f16"), timed as the wall
 * clock from encoding to completion and as the GPU's own start-to-end time, reps interleaved
 * with Accelerate's sgemm on the same inputs; the error of each against the f64 product of the
 * same (f32-rounded) inputs, max-norm relative to max|C|, as bench_fmm's err64.
 *   usage: gpu_gemm n [reps] [mps|graph|f16]   (graph: MPSGraph's matrixMultiplication, f32)
 * A check explains the bit-identical f32 results: 64 sampled outputs are recomputed as the
 * sequential k-ordered FMA chain, and the count of exact matches with the GPU's and with
 * Accelerate's result is printed (both accumulate in k order, so they agree bit for bit).
 * Build: see Makefile (clang -fobjc-arc, frameworks Foundation Metal MetalPerformanceShaders Accelerate). */
#import <Foundation/Foundation.h>
#import <Metal/Metal.h>
#import <MetalPerformanceShaders/MetalPerformanceShaders.h>
#import <MetalPerformanceShadersGraph/MetalPerformanceShadersGraph.h>
#include <Accelerate/Accelerate.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static int cmpd(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return x < y ? -1 : x > y;
}

int main(int argc, char **argv) {
    size_t n = argc > 1 ? strtoull(argv[1], NULL, 10) : 4096;
    int reps = argc > 2 ? atoi(argv[2]) : 5;
    int half = argc > 3 && !strcmp(argv[3], "f16");
    int graph = argc > 3 && !strcmp(argv[3], "graph");
    if (reps < 1 || reps > 32) reps = 5;
    @autoreleasepool {
        id<MTLDevice> dev = MTLCreateSystemDefaultDevice();
        if (!dev) { fprintf(stderr, "no Metal device\n"); return 1; }
        size_t nn = n * n, page = 16384;
        size_t fbytes = ((nn * 4 + page - 1) / page) * page, hbytes = ((nn * 2 + page - 1) / page) * page;
        float *A, *B, *C;
        if (posix_memalign((void **)&A, page, fbytes) || posix_memalign((void **)&B, page, fbytes) ||
            posix_memalign((void **)&C, page, fbytes)) { fprintf(stderr, "alloc\n"); return 1; }
        uint64_t s = 0x9e3779b97f4a7c15ull;
        const char *seed = getenv("FMM_SEED");
        if (seed) s ^= (uint64_t)strtoull(seed, NULL, 0) * 0xbf58476d1ce4e5b9ull;
        for (size_t i = 0; i < nn; i++) {
            s ^= s << 13; s ^= s >> 7; s ^= s << 17;
            A[i] = (float)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
            s ^= s << 13; s ^= s >> 7; s ^= s << 17;
            B[i] = (float)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
        }
        /* the GPU's operands: the f32 arrays themselves, or f16 copies */
        id<MTLBuffer> bA, bB, bC;
        _Float16 *Ah = NULL, *Bh = NULL;
        if (half) {
            if (posix_memalign((void **)&Ah, page, hbytes) || posix_memalign((void **)&Bh, page, hbytes)) return 1;
            for (size_t i = 0; i < nn; i++) { Ah[i] = (_Float16)A[i]; Bh[i] = (_Float16)B[i]; }
            bA = [dev newBufferWithBytesNoCopy:Ah length:hbytes options:MTLResourceStorageModeShared deallocator:nil];
            bB = [dev newBufferWithBytesNoCopy:Bh length:hbytes options:MTLResourceStorageModeShared deallocator:nil];
        } else {
            bA = [dev newBufferWithBytesNoCopy:A length:fbytes options:MTLResourceStorageModeShared deallocator:nil];
            bB = [dev newBufferWithBytesNoCopy:B length:fbytes options:MTLResourceStorageModeShared deallocator:nil];
        }
        bC = [dev newBufferWithBytesNoCopy:C length:fbytes options:MTLResourceStorageModeShared deallocator:nil];
        if (!bA || !bB || !bC) { fprintf(stderr, "buffer wrap failed\n"); return 1; }
        MPSDataType it = half ? MPSDataTypeFloat16 : MPSDataTypeFloat32;
        MPSMatrixDescriptor *dIn = [MPSMatrixDescriptor matrixDescriptorWithRows:n columns:n rowBytes:n * (half ? 2 : 4) dataType:it];
        MPSMatrixDescriptor *dOut = [MPSMatrixDescriptor matrixDescriptorWithRows:n columns:n rowBytes:n * 4 dataType:MPSDataTypeFloat32];
        MPSMatrix *mA = [[MPSMatrix alloc] initWithBuffer:bA descriptor:dIn];
        MPSMatrix *mB = [[MPSMatrix alloc] initWithBuffer:bB descriptor:dIn];
        MPSMatrix *mC = [[MPSMatrix alloc] initWithBuffer:bC descriptor:dOut];
        MPSMatrixMultiplication *mm = [[MPSMatrixMultiplication alloc] initWithDevice:dev transposeLeft:NO transposeRight:NO
                                                                           resultRows:n resultColumns:n interiorColumns:n
                                                                                alpha:1.0 beta:0.0];
        id<MTLCommandQueue> q = [dev newCommandQueue];
        MPSGraph *g = nil;
        MPSGraphTensor *tA = nil, *tB = nil, *tC = nil;
        MPSGraphTensorData *gA = nil, *gB = nil, *gC = nil;
        if (graph) {
            g = [MPSGraph new];
            NSArray<NSNumber *> *shape = @[@(n), @(n)];
            tA = [g placeholderWithShape:shape dataType:MPSDataTypeFloat32 name:@"A"];
            tB = [g placeholderWithShape:shape dataType:MPSDataTypeFloat32 name:@"B"];
            tC = [g matrixMultiplicationWithPrimaryTensor:tA secondaryTensor:tB name:@"C"];
            gA = [[MPSGraphTensorData alloc] initWithMTLBuffer:bA shape:shape dataType:MPSDataTypeFloat32];
            gB = [[MPSGraphTensorData alloc] initWithMTLBuffer:bB shape:shape dataType:MPSDataTypeFloat32];
            gC = [[MPSGraphTensorData alloc] initWithMTLBuffer:bC shape:shape dataType:MPSDataTypeFloat32];
        }
        float *Cs = malloc(nn * sizeof(float));
        double tw[32], tg[32], ts[32];
        /* warm-up (pipeline compile, clocks), then interleaved rounds: GPU, then Accelerate */
        for (int r = -1; r < reps; r++) {
            double t0 = now(), gt = 0;
            if (graph) {
                [g runWithMTLCommandQueue:q feeds:@{tA : gA, tB : gB} targetOperations:nil resultsDictionary:@{tC : gC}];
            } else {
                id<MTLCommandBuffer> cb = [q commandBuffer];
                [mm encodeToCommandBuffer:cb leftMatrix:mA rightMatrix:mB resultMatrix:mC];
                [cb commit];
                [cb waitUntilCompleted];
                if (cb.status != MTLCommandBufferStatusCompleted) { fprintf(stderr, "GPU error %s\n", cb.error.localizedDescription.UTF8String); return 1; }
                gt = cb.GPUEndTime - cb.GPUStartTime;
            }
            double t1 = now();
            double t2 = now();
            cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0f, A, (int)n, B, (int)n, 0.0f, Cs, (int)n);
            double t3 = now();
            if (r >= 0) { tw[r] = t1 - t0; tg[r] = gt; ts[r] = t3 - t2; }
        }
        /* the exact reference: the f64 product of the f32-rounded inputs (f16-rounded for "f16": the
         * GPU's actual inputs; the f32 inputs' product is reported too, as the error a user sees) */
        double *A64 = malloc(nn * 8), *B64 = malloc(nn * 8), *R64 = malloc(nn * 8);
        for (size_t i = 0; i < nn; i++) { A64[i] = A[i]; B64[i] = B[i]; }
        cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0, A64, (int)n, B64, (int)n, 0.0, R64, (int)n);
        double rmax = 0, eg = 0, es = 0, egs = 0, cmax = 0;
        for (size_t i = 0; i < nn; i++) rmax = fmax(rmax, fabs(R64[i]));
        for (size_t i = 0; i < nn; i++) {
            eg = fmax(eg, fabs((double)C[i] - R64[i]));
            es = fmax(es, fabs((double)Cs[i] - R64[i]));
            egs = fmax(egs, fabs((double)C[i] - (double)Cs[i]));
            cmax = fmax(cmax, fabs((double)Cs[i]));
        }
        double egh = -1;
        if (half) {   /* against the product of what the GPU was given */
            for (size_t i = 0; i < nn; i++) { A64[i] = (double)Ah[i]; B64[i] = (double)Bh[i]; }
            cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0, A64, (int)n, B64, (int)n, 0.0, R64, (int)n);
            double rm = 0; egh = 0;
            for (size_t i = 0; i < nn; i++) rm = fmax(rm, fabs(R64[i]));
            for (size_t i = 0; i < nn; i++) egh = fmax(egh, fabs((double)C[i] - R64[i]));
            egh /= rm;
        }
        /* the k-ordered FMA chain on 64 sampled outputs */
        int same_g = 0, same_s = 0;
        uint64_t z = 12345;
        for (int t = 0; t < 64; t++) {
            z ^= z << 13; z ^= z >> 7; z ^= z << 17;
            size_t i = (z >> 11) % n;
            z ^= z << 13; z ^= z >> 7; z ^= z << 17;
            size_t j = (z >> 11) % n;
            float c = 0;
            if (half) for (size_t k = 0; k < n; k++) c = fmaf((float)Ah[i * n + k], (float)Bh[k * n + j], c);
            else for (size_t k = 0; k < n; k++) c = fmaf(A[i * n + k], B[k * n + j], c);
            same_g += C[i * n + j] == c;
            same_s += Cs[i * n + j] == c;
        }
        qsort(tw, reps, sizeof(double), cmpd);
        qsort(tg, reps, sizeof(double), cmpd);
        qsort(ts, reps, sizeof(double), cmpd);
        double flop = 2.0 * n * n * n;
        printf("gpu_%s  n=%-6zu f32  min %8.3f s  med %8.3f s  gpu-time min %8.3f med %8.3f  %7.1f GFLOP/s(2n^3, med wall)"
               "  err64 %.2e  vs-sgemm %.2e%s\n",
               half ? "mps16" : graph ? "graph" : "mps", n, tw[0], tw[reps / 2], tg[0], tg[reps / 2], flop / tw[reps / 2] / 1e9, eg / rmax, egs / cmax,
               "");
        printf("           n=%-6zu   k-ordered FMA chain on 64 sampled outputs: equals the GPU's result at %d, Accelerate's at %d\n", n, same_g, same_s);
        if (half) printf("gpu_mps16 n=%-6zu   error against the product of the f16-rounded inputs %.2e\n", n, egh);
        printf("sgemm      n=%-6zu f32  min %8.3f s  med %8.3f s  %7.1f GFLOP/s(2n^3)  err64 %.2e  (Accelerate, same inputs; speedup gpu/sgemm %.3f by medians)\n",
               n, ts[0], ts[reps / 2], flop / ts[reps / 2] / 1e9, es / rmax, ts[reps / 2] / tw[reps / 2]);
        fflush(stdout);
    }
    return 0;
}
