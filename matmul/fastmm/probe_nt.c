/* probe_nt.c: do the passes starve the SME units through the cache, and do non-temporal stores
 * help?  For a fixed time, concurrently: k single-threaded GEMM streams of size m (each on its
 * own operands) and w threads streaming dst = a + b over large arrays (two blocks read, one
 * written, like a pass with few streams), with ordinary stores, with non-temporal stores (STNP,
 * which Apple's own memmove uses for large copies) or with the reads non-temporal too (LDNP).
 *   probe_nt [-t f|d] [-n 768] [-k 6] [-w 2] [-s 3] [-m 0|1|2] [-q i|b]
 * -m: 0 ordinary, 1 STNP stores, 2 STNP stores and LDNP loads; -q b: the pass threads on the
 * efficiency cores (background quality of service). */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <arm_neon.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static void *alloc_t(size_t bytes) {
    void *p = NULL;
    if (posix_memalign(&p, 16384, bytes)) exit(1);
    memset(p, 1, bytes);
    return p;
}
static int f64, mode, qos = 'i';
static size_t n = 768;
static atomic_int stop;
#define REGION ((size_t)192 << 20)      /* bytes per array per pass thread */
typedef struct { int pass; double flops, secs, bytes; } worker_t;

static void add_pass(double *restrict d, const double *restrict a, const double *restrict b, size_t cnt) {
    if (mode == 0) {
        for (size_t i = 0; i < cnt; i += 4) {
            vst1q_f64(d + i, vaddq_f64(vld1q_f64(a + i), vld1q_f64(b + i)));
            vst1q_f64(d + i + 2, vaddq_f64(vld1q_f64(a + i + 2), vld1q_f64(b + i + 2)));
        }
    } else if (mode == 1) {
        for (size_t i = 0; i < cnt; i += 4) {
            float64x2_t x = vaddq_f64(vld1q_f64(a + i), vld1q_f64(b + i)), y = vaddq_f64(vld1q_f64(a + i + 2), vld1q_f64(b + i + 2));
            __asm__ volatile("stnp %q0, %q1, [%2]" : : "w"(x), "w"(y), "r"(d + i) : "memory");
        }
    } else {
        for (size_t i = 0; i < cnt; i += 4) {
            float64x2_t a0, a1, b0, b1;
            __asm__ volatile("ldnp %q0, %q1, [%2]" : "=w"(a0), "=w"(a1) : "r"(a + i) : "memory");
            __asm__ volatile("ldnp %q0, %q1, [%2]" : "=w"(b0), "=w"(b1) : "r"(b + i) : "memory");
            float64x2_t x = vaddq_f64(a0, b0), y = vaddq_f64(a1, b1);
            __asm__ volatile("stnp %q0, %q1, [%2]" : : "w"(x), "w"(y), "r"(d + i) : "memory");
        }
    }
}

static void *worker(void *p) {
    worker_t *w = p;
    pthread_set_qos_class_self_np(w->pass && qos == 'b' ? QOS_CLASS_BACKGROUND : QOS_CLASS_USER_INTERACTIVE, 0);
    if (w->pass) {
        double *a = alloc_t(REGION), *b = alloc_t(REGION), *d = alloc_t(REGION);
        size_t cnt = REGION / 8;
        double t0 = now();
        long reps = 0;
        while (!atomic_load(&stop)) {
            for (size_t c = 0; c < cnt && !atomic_load(&stop); c += 1 << 18) add_pass(d + c, a + c, b + c, 1 << 18), reps++;
        }
        w->secs = now() - t0;
        w->bytes = 3.0 * 8 * (double)(1 << 18) * reps;
        free(a); free(b); free(d);
    } else {
        BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
        size_t es = f64 ? 8 : 4, nn = n * n;
        void *A = alloc_t(nn * es), *B = alloc_t(nn * es), *C = alloc_t(nn * es);
        memset(A, 0, nn * es); memset(B, 0, nn * es);
        long calls = 0;
        double t0 = now();
        while (!atomic_load(&stop)) {
            if (f64) cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0, A, (int)n, B, (int)n, 0.0, C, (int)n);
            else cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0f, A, (int)n, B, (int)n, 0.0f, C, (int)n);
            calls++;
        }
        w->secs = now() - t0;
        w->flops = 2.0 * (double)n * n * n * calls;
        free(A); free(B); free(C);
    }
    return NULL;
}

int main(int argc, char **argv) {
    int k = 6, wn = 2;
    double secs = 3;
    for (int i = 1; i + 1 < argc; i += 2) {
        if (!strcmp(argv[i], "-t")) f64 = argv[i + 1][0] == 'd';
        else if (!strcmp(argv[i], "-n")) n = (size_t)atol(argv[i + 1]);
        else if (!strcmp(argv[i], "-k")) k = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-w")) wn = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-s")) secs = atof(argv[i + 1]);
        else if (!strcmp(argv[i], "-m")) mode = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-q")) qos = argv[i + 1][0];
    }
    for (int phase = 0; phase < 3; phase++) {
        int ks = phase == 1 ? 0 : k, ws = phase == 0 ? 0 : wn;
        worker_t wk[64] = {{0}};
        pthread_t th[64];
        atomic_store(&stop, 0);
        for (int i = 0; i < ks + ws; i++) {
            wk[i].pass = i >= ks;
            pthread_create(&th[i], NULL, worker, &wk[i]);
        }
        struct timespec ts = {(time_t)secs + 1, 0};     /* a second for the allocations */
        nanosleep(&ts, NULL);
        atomic_store(&stop, 1);
        double gs = 0, gb = 0;
        for (int i = 0; i < ks + ws; i++) {
            pthread_join(th[i], NULL);
            if (wk[i].pass) gb += wk[i].bytes / wk[i].secs / 1e9;
            else gs += wk[i].flops / wk[i].secs / 1e9;
        }
        printf("%s m=%zu mode %d qos %c  %d SME streams + %d pass threads:  GEMM %7.1f GFLOP/s   pass %6.1f GB/s\n",
               f64 ? "f64" : "f32", n, mode, qos, ks, ws, gs, gb);
        fflush(stdout);
    }
    return 0;
}
