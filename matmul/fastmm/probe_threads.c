/* probe_threads.c: how much of the M4 Pro does Accelerate's GEMM use, and what is left for the
 * other cores?  For a fixed time, concurrently:
 *   -g G   G >= 1: G threads, each a stream of single-threaded GEMMs of size n on its own operands
 *          G = 0: one stream of Accelerate's own multi-threaded GEMM (as bench_fmm calls it)
 *          G = -1: no GEMM
 *   -v V   V threads of register-only NEON fused multiply-adds (the vector units' peak, no memory)
 * Reports GEMM and NEON GFLOP/s and the cores kept busy (process CPU time / wall time).
 *
 *   probe_threads [-t f|d] [-n 2048] [-g 0] [-v 0] [-s 3]
 */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <arm_neon.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static double cpu_time(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + 1e-6 * ru.ru_utime.tv_usec + (double)ru.ru_stime.tv_sec
           + 1e-6 * ru.ru_stime.tv_usec;
}

static atomic_int stop;
static int f64;
static size_t n = 2048;

typedef struct {
    int single;
    double flops, secs;
} worker_t;

static void *gemm_worker(void *p) {
    worker_t *w = p;
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    if (w->single) BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
    size_t bytes = n * n * (f64 ? 8 : 4);
    void *A, *B, *C;
    if (posix_memalign(&A, 16384, bytes) || posix_memalign(&B, 16384, bytes) || posix_memalign(&C, 16384, bytes)) exit(1);
    for (size_t i = 0; i < n * n; i++) {
        if (f64) { ((double *)A)[i] = 1.0 / (1 + i % 7); ((double *)B)[i] = 1.0 / (1 + i % 5); }
        else { ((float *)A)[i] = 1.0f / (1 + i % 7); ((float *)B)[i] = 1.0f / (1 + i % 5); }
    }
    long calls = 0;
    double t0 = now();
    while (!atomic_load(&stop)) {
        if (f64)
            cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0, A, (int)n, B,
                        (int)n, 0.0, C, (int)n);
        else
            cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0f, A, (int)n, B,
                        (int)n, 0.0f, C, (int)n);
        calls++;
    }
    w->secs = now() - t0;
    w->flops = 2.0 * (double)n * n * n * calls;
    free(A); free(B); free(C);
    return NULL;
}

static volatile double sink;
static volatile double vb = 0.9999999, vc = 1e-9, va = 1.0;   /* opaque to the compiler: no constant folding */

/* 16 independent accumulator chains: enough to keep 4 FMA pipes busy at 4 cycles latency */
static void *neon_worker(void *p) {
    worker_t *w = p;
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    long iters = 0;
    double t0 = now();
    if (f64) {
        float64x2_t a[16];
        const float64x2_t b = vdupq_n_f64(vb), c = vdupq_n_f64(vc);
        for (int k = 0; k < 16; k++) a[k] = vdupq_n_f64(va + k);
        while (!atomic_load_explicit(&stop, memory_order_relaxed)) {
            for (int i = 0; i < 4096; i++)
                for (int k = 0; k < 16; k++) a[k] = vfmaq_f64(a[k], b, c);
            iters += 4096;
        }
        double s = 0;
        for (int k = 0; k < 16; k++) s += vgetq_lane_f64(a[k], 0) + vgetq_lane_f64(a[k], 1);
        sink = s;
        w->flops = (double)iters * 16 * 2 * 2;
    } else {
        float32x4_t a[16];
        const float32x4_t b = vdupq_n_f32((float)vb), c = vdupq_n_f32((float)vc);
        for (int k = 0; k < 16; k++) a[k] = vdupq_n_f32((float)va + k);
        while (!atomic_load_explicit(&stop, memory_order_relaxed)) {
            for (int i = 0; i < 4096; i++)
                for (int k = 0; k < 16; k++) a[k] = vfmaq_f32(a[k], b, c);
            iters += 4096;
        }
        float s = 0;
        for (int k = 0; k < 16; k++) s += vaddvq_f32(a[k]);
        sink = s;
        w->flops = (double)iters * 16 * 4 * 2;
    }
    w->secs = now() - t0;
    return NULL;
}

int main(int argc, char **argv) {
    int g = 0, v = 0;
    double secs = 3;
    for (int i = 1; i + 1 < argc; i += 2) {
        if (!strcmp(argv[i], "-t")) f64 = argv[i + 1][0] == 'd';
        else if (!strcmp(argv[i], "-n")) n = (size_t)atol(argv[i + 1]);
        else if (!strcmp(argv[i], "-g")) g = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-v")) v = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-s")) secs = atof(argv[i + 1]);
    }
    int ng = g < 0 ? 0 : g == 0 ? 1 : g;
    worker_t ws[64] = {{0}};
    pthread_t th[64];
    double c0 = cpu_time(), t0 = now();
    for (int i = 0; i < ng; i++) {
        ws[i].single = g > 0;
        pthread_create(&th[i], NULL, gemm_worker, &ws[i]);
    }
    for (int i = 0; i < v; i++) pthread_create(&th[ng + i], NULL, neon_worker, &ws[ng + i]);
    struct timespec ts = {(time_t)secs, (long)((secs - (time_t)secs) * 1e9)};
    nanosleep(&ts, NULL);
    atomic_store(&stop, 1);
    for (int i = 0; i < ng + v; i++) pthread_join(th[i], NULL);
    double wall = now() - t0, cpu = cpu_time() - c0;
    double gr = 0, vr = 0;
    for (int i = 0; i < ng; i++) gr += ws[i].flops / ws[i].secs / 1e9;
    for (int i = 0; i < v; i++) vr += ws[ng + i].flops / ws[ng + i].secs / 1e9;
    printf("%s n=%zu gemm-threads %-2d neon-threads %-2d  GEMM %7.1f GFLOP/s  NEON %7.1f GFLOP/s  cores busy %.2f\n",
           f64 ? "f64" : "f32", n, g, v, gr, vr, cpu / wall);
    return 0;
}
