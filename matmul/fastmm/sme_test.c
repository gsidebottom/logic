/* sme_test.c: the SME leaf kernel of sme_gemm.h against Accelerate's GEMM on the products of a
 * level: r products of shape (m x k)(k x n) taken in turn by t threads, as the library's GEMM
 * streams do (single-threaded cblas calls against sme_?gemm_at calls), caches evicted first.
 * Checks the results agree (they should be bit-identical) and prints both rates.
 *
 *   sme_test [-t f|d] [-T threads] [-r products] [-l aligned|odd] m k n [m k n ...]
 * -l aligned: leading dimensions equal to the widths (rows a power-of-two multiple apart);
 * -l odd (default): sme_ld, an odd number of cache lines. */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <dispatch/dispatch.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "sme_gemm.h"

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
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

#define BENCH(T, SUF, GEMM, KERN)                                                                                \
    static void bench_##SUF(size_t m, size_t k, size_t n, int threads, int r, int odd) {                         \
        size_t lda = k, ldat = odd ? sme_ld(m, sizeof(T)) : m, ldb = odd ? sme_ld(n, sizeof(T)) : n,             \
               ldc = odd ? sme_ld(n, sizeof(T)) : n, ldbg = n;                                                   \
        size_t sa = m * lda, sat = k * ldat, sb = k * ldb, sbg = k * ldbg, sc = m * ldc;                         \
        T *A, *AT, *B, *BG, *C, *D;                                                                              \
        posix_memalign((void **)&A, 16384, (size_t)r * sa * sizeof(T));                                          \
        posix_memalign((void **)&AT, 16384, (size_t)r * sat * sizeof(T));                                        \
        posix_memalign((void **)&B, 16384, (size_t)r * sb * sizeof(T));                                          \
        posix_memalign((void **)&BG, 16384, (size_t)r * sbg * sizeof(T));                                        \
        posix_memalign((void **)&C, 16384, (size_t)r * sc * sizeof(T));                                          \
        posix_memalign((void **)&D, 16384, (size_t)r * m * n * sizeof(T));                                       \
        uint64_t s = 0x2545f4914f6cdd1dull;                                                                      \
        for (int q = 0; q < r; q++) {                                                                            \
            for (size_t i = 0; i < m; i++)                                                                       \
                for (size_t p = 0; p < k; p++) {                                                                 \
                    s ^= s << 13; s ^= s >> 7; s ^= s << 17;                                                     \
                    T v = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);                                   \
                    A[q * sa + i * lda + p] = v;                                                                 \
                    AT[q * sat + p * ldat + i] = v;                                                              \
                }                                                                                                \
            for (size_t p = 0; p < k; p++)                                                                       \
                for (size_t j = 0; j < n; j++) {                                                                 \
                    s ^= s << 13; s ^= s >> 7; s ^= s << 17;                                                     \
                    T v = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);                                   \
                    B[q * sb + p * ldb + j] = v;                                                                 \
                    BG[q * sbg + p * ldbg + j] = v;                                                              \
                }                                                                                                \
        }                                                                                                        \
        memset(C, 0, (size_t)r * sc * sizeof(T));                                                                \
        memset(D, 0, (size_t)r * m * n * sizeof(T));                                                             \
        dispatch_queue_t qu = dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0);                          \
        double best[2] = {1e9, 1e9};                                                                             \
        for (int rep = 0; rep < 5; rep++) {                                                                      \
            atomic_int next = 0;                                                                                 \
            atomic_int *pn = &next;                                                                              \
            evict();                                                                                             \
            double t0 = now();                                                                                   \
            dispatch_apply((size_t)threads, qu, ^(size_t w) {                                                    \
                (void)w;                                                                                         \
                enum BLAS_THREADING old = BLASGetThreading();                                                    \
                BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);                                                \
                for (int q; (q = atomic_fetch_add(pn, 1)) < r;)                                                  \
                    GEMM(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)m, (int)n, (int)k, 1, A + q * sa, (int)lda, \
                         BG + q * sbg, (int)ldbg, 0, D + (size_t)q * m * n, (int)n);                             \
                BLASSetThreading(old);                                                                           \
            });                                                                                                  \
            double t1 = now();                                                                                   \
            atomic_store(pn, 0);                                                                                 \
            evict();                                                                                             \
            double t2 = now();                                                                                   \
            dispatch_apply((size_t)threads, qu, ^(size_t w) {                                                    \
                (void)w;                                                                                         \
                for (int q; (q = atomic_fetch_add(pn, 1)) < r;)                                                  \
                    KERN(m, k, n, AT + q * sat, ldat, B + q * sb, ldb, C + q * sc, ldc);                         \
            });                                                                                                  \
            double t3 = now();                                                                                   \
            if (t1 - t0 < best[0]) best[0] = t1 - t0;                                                            \
            if (t3 - t2 < best[1]) best[1] = t3 - t2;                                                            \
        }                                                                                                        \
        double err = 0, mx = 0;                                                                                  \
        for (int q = 0; q < r; q++)                                                                              \
            for (size_t i = 0; i < m; i++)                                                                       \
                for (size_t j = 0; j < n; j++) {                                                                 \
                    double d = (double)C[q * sc + i * ldc + j] - (double)D[(size_t)q * m * n + i * n + j];       \
                    if (d < 0) d = -d;                                                                           \
                    if (d > err) err = d;                                                                        \
                    double v = D[(size_t)q * m * n + i * n + j];                                                 \
                    if (v < 0) v = -v;                                                                           \
                    if (v > mx) mx = v;                                                                          \
                }                                                                                                \
        double fl = 2.0 * m * k * n * r;                                                                         \
        printf("%s %5zux%5zux%5zu r=%3d threads=%2d ld=%s  accelerate %7.1f GF  sme %7.1f GF  ratio %.3f  maxdiff/max %.1e\n", \
               #SUF, m, k, n, r, threads, odd ? "odd" : "aligned", fl / best[0] / 1e9, fl / best[1] / 1e9,       \
               best[0] / best[1], err / mx);                                                                     \
        fflush(stdout);                                                                                          \
        free(A); free(AT); free(B); free(BG); free(C); free(D);                                                  \
    }
BENCH(double, d, cblas_dgemm, sme_dgemm_at)
BENCH(float, f, cblas_sgemm, sme_sgemm_at)

int main(int argc, char **argv) {
    char type = 'd';
    int threads = 6, r = 0, odd = 1, i = 1;
    for (; i + 1 < argc && argv[i][0] == '-'; i += 2) {
        if (!strcmp(argv[i], "-t")) type = argv[i + 1][0];
        else if (!strcmp(argv[i], "-T")) threads = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-r")) r = atoi(argv[i + 1]);
        else if (!strcmp(argv[i], "-l")) odd = strcmp(argv[i + 1], "aligned") != 0;
    }
    for (; i + 2 < argc; i += 3) {
        size_t m = (size_t)atol(argv[i]), k = (size_t)atol(argv[i + 1]), n = (size_t)atol(argv[i + 2]);
        int rr = r;
        if (!rr) {                              /* about 0.3 s of products, at least 12, at most 480 */
            double per = 2.0 * m * k * n / (type == 'd' ? 1e12 : 3.8e12);
            rr = (int)(0.3 / per);
            if (rr < 12) rr = 12;
            if (rr > 480) rr = 480;
            double bytes = (double)rr * (3.0 * m * k + 2.0 * k * n + 2.0 * m * n) * (type == 'd' ? 8 : 4);
            while (rr > 12 && bytes > 12e9) { rr /= 2; bytes /= 2; }
        }
        if (type == 'd') bench_d(m, k, n, threads, rr, odd);
        else bench_f(m, k, n, threads, rr, odd);
    }
    return 0;
}
