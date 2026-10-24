/* neon_test.c: the NEON GEMM of neon_gemm.h against Accelerate: correctness, one core, several
 * cores sharing a product by row slabs, and NEON threads running beside SME streams.
 *
 *   neon_test [-t f|d] [-n 1024] [-w 7] [-k 3] [-s 3]
 *     one core and w cores on one product, then for s seconds k single-threaded SME GEMM
 *     streams and w NEON threads, each a stream of whole products on its own operands
 */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <dispatch/dispatch.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "neon_gemm.h"

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void *alloc_t(size_t bytes) {
    void *p = NULL;
    if (posix_memalign(&p, 16384, bytes ? bytes : 16)) exit(1);
    return p;
}

static int f64;
static size_t n = 1024;
static atomic_int stop;

static void fill(void *X, size_t cnt, unsigned seed) {
    uint64_t s = 0x9e3779b97f4a7c15ull ^ seed;
    for (size_t i = 0; i < cnt; i++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        double v = (double)(s >> 11) / 9007199254740992.0 * 2 - 1;
        if (f64) ((double *)X)[i] = v;
        else ((float *)X)[i] = (float)v;
    }
}

static void neon_rows(const void *A, const void *B, void *C, size_t r0, size_t r1, void *pa, void *pb) {
    if (f64) neon_dgemm_rows(n, A, n, B, n, C, n, r0, r1, pa, pb);
    else neon_sgemm_rows(n, A, n, B, n, C, n, r0, r1, pa, pb);
}

static void sme_gemm(const void *A, const void *B, void *C) {
    if (f64)
        cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0, A, (int)n, B, (int)n,
                    0.0, C, (int)n);
    else
        cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0f, A, (int)n, B, (int)n,
                    0.0f, C, (int)n);
}

typedef struct {
    int neon;
    double flops, secs;
} worker_t;

static void *worker(void *p) {
    worker_t *w = p;
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
    size_t es = f64 ? 8 : 4, nn = n * n;
    void *A = alloc_t(nn * es), *B = alloc_t(nn * es), *C = alloc_t(nn * es);
    void *pa = alloc_t(n * NEON_KC * es), *pb = alloc_t(n * NEON_KC * es);
    fill(A, nn, 1);
    fill(B, nn, 2);
    long calls = 0;
    double t0 = now();
    while (!atomic_load(&stop)) {
        if (w->neon) neon_rows(A, B, C, 0, n, pa, pb);
        else sme_gemm(A, B, C);
        calls++;
    }
    w->secs = now() - t0;
    w->flops = 2.0 * (double)n * n * n * calls;
    free(A); free(B); free(C); free(pa); free(pb);
    return NULL;
}

int main(int argc, char **argv) {
    int wn = 7, k = 3;
    double secs = 3;
    for (int i = 1; i + 1 < argc; i += 2) {
        if (!strcmp(argv[i], "-t")) f64 = argv[i + 1][0] == 'd';
        else if (!strcmp(argv[i], "-n")) n = (size_t)atol(argv[i + 1]);
        else if (!strcmp(argv[i], "-w")) wn = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-k")) k = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-s")) secs = atof(argv[i + 1]);
    }
    size_t es = f64 ? 8 : 4, nn = n * n, mr = f64 ? 4 : 8;
    const char *tn = f64 ? "f64" : "f32";
    double peak = f64 ? 59 : 117;   /* one core's register-only FMA rate (probe_threads) */
    void *A = alloc_t(nn * es), *B = alloc_t(nn * es), *C = alloc_t(nn * es), *R = alloc_t(nn * es);
    fill(A, nn, 1);
    fill(B, nn, 2);
    sme_gemm(A, B, R);
    /* one core */
    void *pa = alloc_t(n * NEON_KC * es), *pb = alloc_t(n * NEON_KC * es);
    double best = 1e30;
    for (int rep = 0; rep < 3; rep++) {
        double t = now();
        neon_rows(A, B, C, 0, n, pa, pb);
        t = now() - t;
        if (t < best) best = t;
    }
    double err = 0, mx = 0;
    for (size_t i = 0; i < nn; i++) {
        double r = f64 ? ((double *)R)[i] : ((float *)R)[i], c = f64 ? ((double *)C)[i] : ((float *)C)[i];
        err = fmax(err, fabs(r - c));
        mx = fmax(mx, fabs(r));
    }
    double gf = 2.0 * nn * n / best / 1e9;
    printf("%s n=%zu  one core: %.4f s  %6.1f GFLOP/s (%.0f%% of %.0f)  max rel err vs Accelerate %.2e\n", tn, n,
           best, gf, 100 * gf / peak, peak, err / mx);
    /* wn cores on one product, row slabs */
    if (wn > 0) {
        size_t slab = (n / wn + mr - 1) / mr * mr;
        void **pas = calloc(wn, sizeof(void *)), **pbs = calloc(wn, sizeof(void *));
        for (int w = 0; w < wn; w++) { pas[w] = alloc_t(n * NEON_KC * es); pbs[w] = alloc_t(n * NEON_KC * es); }
        best = 1e30;
        for (int rep = 0; rep < 3; rep++) {
            double t = now();
            dispatch_apply((size_t)wn, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t w) {
                size_t r0 = w * slab, r1 = r0 + slab < n ? r0 + slab : n;
                if (r0 < r1) neon_rows(A, B, C, r0, r1, pas[w], pbs[w]);
            });
            t = now() - t;
            if (t < best) best = t;
        }
        gf = 2.0 * nn * n / best / 1e9;
        printf("%s n=%zu  %d cores, row slabs: %.4f s  %6.1f GFLOP/s (%.0f%% of %d x %.0f)\n", tn, n, wn, best, gf,
               100 * gf / (wn * peak), wn, peak);
    }
    /* k SME streams beside wn NEON threads */
    for (int phase = 0; phase < 3; phase++) {
        int ks = phase == 1 ? 0 : k, ws = phase == 0 ? 0 : wn;
        if (ks + ws == 0) continue;
        worker_t wk[64] = {{0}};
        pthread_t th[64];
        atomic_store(&stop, 0);
        for (int i = 0; i < ks + ws; i++) {
            wk[i].neon = i >= ks;
            pthread_create(&th[i], NULL, worker, &wk[i]);
        }
        struct timespec ts = {(time_t)secs, (long)((secs - (time_t)secs) * 1e9)};
        nanosleep(&ts, NULL);
        atomic_store(&stop, 1);
        double gs = 0, gn = 0;
        for (int i = 0; i < ks + ws; i++) {
            pthread_join(th[i], NULL);
            if (wk[i].neon) gn += wk[i].flops / wk[i].secs / 1e9;
            else gs += wk[i].flops / wk[i].secs / 1e9;
        }
        printf("%s n=%zu  %d SME streams + %d NEON threads: SME %7.1f + NEON %6.1f = %7.1f GFLOP/s\n", tn, n, ks, ws, gs,
               gn, gs + gn);
    }
    return 0;
}
