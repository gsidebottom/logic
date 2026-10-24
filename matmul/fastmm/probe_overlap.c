/* probe_overlap.c: can the fused passes run beside the SME GEMM streams?  For a fixed time,
 * concurrently: k single-threaded GEMM streams of size m (each on its own operands) and w
 * threads running our 48-scheme's L pass at block size m (16 blocks of a 4m x 4m matrix in, 48
 * padded blocks out, the rows split among the threads, pass after pass).  Reports GEMM GFLOP/s
 * and pass GB/s alone and together.
 *
 *   probe_overlap [-t f|d] [-n 1024] [-k 3] [-w 7] [-s 3]
 */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "kernels.h"

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
#define PAD 1040

/* the pass: shared input and output block sets, each thread its own rows */
static void *pin[16], *pout[48];
static atomic_long rows_done;

typedef struct {
    int pass;
    size_t r0, r1;
    double flops, secs;
} worker_t;

static void *worker(void *p) {
    worker_t *w = p;
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    double t0 = now();
    if (w->pass) {
        long rows = 0;
        while (!atomic_load(&stop)) {
            if (f64) dps48_L_d(n, 4 * n, n, (const double *const *)pin, (double *const *)pout, w->r0, w->r1);
            else dps48_L_f(n, 4 * n, n, (const float *const *)pin, (float *const *)pout, w->r0, w->r1);
            rows += (long)(w->r1 - w->r0);
        }
        atomic_fetch_add(&rows_done, rows);
    } else {
        BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
        size_t es = f64 ? 8 : 4, nn = n * n;
        void *A = alloc_t(nn * es), *B = alloc_t(nn * es), *C = alloc_t(nn * es);
        memset(A, 0, nn * es);
        memset(B, 0, nn * es);
        long calls = 0;
        while (!atomic_load(&stop)) {
            if (f64)
                cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0, A, (int)n, B,
                            (int)n, 0.0, C, (int)n);
            else
                cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0f, A, (int)n, B,
                            (int)n, 0.0f, C, (int)n);
            calls++;
        }
        w->flops = 2.0 * (double)n * n * n * calls;
        free(A); free(B); free(C);
    }
    w->secs = now() - t0;
    return NULL;
}

int main(int argc, char **argv) {
    int k = 3, wn = 7;
    double secs = 3;
    for (int i = 1; i + 1 < argc; i += 2) {
        if (!strcmp(argv[i], "-t")) f64 = argv[i + 1][0] == 'd';
        else if (!strcmp(argv[i], "-n")) n = (size_t)atol(argv[i + 1]);
        else if (!strcmp(argv[i], "-k")) k = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-w")) wn = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-s")) secs = atof(argv[i + 1]);
    }
    size_t es = f64 ? 8 : 4;
    char *in = alloc_t(16 * n * n * es), *out = alloc_t(48 * (n * n + PAD) * es);
    memset(in, 0, 16 * n * n * es);
    memset(out, 0, 48 * (n * n + PAD) * es);
    for (int q = 0; q < 16; q++) pin[q] = in + ((q / 4) * n * 4 * n + (q % 4) * n) * es;
    for (int q = 0; q < 48; q++) pout[q] = out + (size_t)q * (n * n + PAD) * es;
    double pass_bytes_per_row = 64.0 * n * es;
    for (int phase = 0; phase < 3; phase++) {
        int ks = phase == 1 ? 0 : k, ws = phase == 0 ? 0 : wn;
        worker_t wk[64] = {{0}};
        pthread_t th[64];
        atomic_store(&stop, 0);
        atomic_store(&rows_done, 0);
        for (int i = 0; i < ks + ws; i++) {
            wk[i].pass = i >= ks;
            if (wk[i].pass) {
                size_t j = i - ks, step = (n + ws - 1) / ws;
                wk[i].r0 = j * step;
                wk[i].r1 = wk[i].r0 + step < n ? wk[i].r0 + step : n;
            }
            pthread_create(&th[i], NULL, worker, &wk[i]);
        }
        double t0 = now();
        struct timespec ts = {(time_t)secs, (long)((secs - (time_t)secs) * 1e9)};
        nanosleep(&ts, NULL);
        atomic_store(&stop, 1);
        double gs = 0;
        for (int i = 0; i < ks + ws; i++) {
            pthread_join(th[i], NULL);
            if (!wk[i].pass) gs += wk[i].flops / wk[i].secs / 1e9;
        }
        double wall = now() - t0;
        double gbs = (double)atomic_load(&rows_done) * pass_bytes_per_row / wall / 1e9;
        printf("%s m=%zu  %d SME streams + %d pass threads:  GEMM %7.1f GFLOP/s   pass %6.1f GB/s\n",
               f64 ? "f64" : "f32", n, ks, ws, gs, gbs);
        fflush(stdout);
    }
    return 0;
}
