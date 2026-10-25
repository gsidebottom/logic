/* test_fmm.c: the library entry points (fmm.h) against Accelerate's GEMM: the plan used,
 * correctness (max-norm relative difference), time (median of 3 after a warm-up), leading
 * dimensions larger than n, an error budget, and sizes the calibration does not cover.
 *
 *   FMM_CALIB_DIR=results build/test_fmm [n ...]
 */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "fmm.h"

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rng = 0x9e3779b97f4a7c15ull;
static double urand(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return (double)(rng >> 11) / 9007199254740992.0 * 2 - 1;
}

static int failures;

/* one case: n x n inside ld x ld storage, precision f64, error budget g */
static void run(size_t n, size_t ld, int f64, double g) {
    size_t es = f64 ? 8 : 4, cnt = n * ld;
    char *A = malloc(cnt * es), *B = malloc(cnt * es), *C = malloc(cnt * es), *R = malloc(cnt * es);
    for (size_t i = 0; i < cnt; i++) {
        double a = urand(), b = urand();
        if (f64) { ((double *)A)[i] = a; ((double *)B)[i] = b; }
        else { ((float *)A)[i] = (float)a; ((float *)B)[i] = (float)b; }
    }
    memset(C, 0, cnt * es);
    double pred, tf[3], tr[3];
    const char *plan = fmm_plan(n, f64, g, &pred);
    for (int rep = -1; rep < 3; rep++) {
        double t = now();
        int rc = f64 ? fmm_dgemm(n, (double *)A, ld, (double *)B, ld, (double *)C, ld, g)
                     : fmm_sgemm(n, (float *)A, ld, (float *)B, ld, (float *)C, ld, g);
        if (rep >= 0) tf[rep] = now() - t;
        if (rc != 0) { printf("fmm returned %d\n", rc); failures++; }
        t = now();
        if (f64)
            cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0, (double *)A, (int)ld,
                        (double *)B, (int)ld, 0.0, (double *)R, (int)ld);
        else
            cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0f, (float *)A, (int)ld,
                        (float *)B, (int)ld, 0.0f, (float *)R, (int)ld);
        if (rep >= 0) tr[rep] = now() - t;
    }
    double err = 0, mx = 0;
    for (size_t i = 0; i < n; i++)
        for (size_t j = 0; j < n; j++) {
            double c = f64 ? ((double *)C)[i * ld + j] : ((float *)C)[i * ld + j];
            double r = f64 ? ((double *)R)[i * ld + j] : ((float *)R)[i * ld + j];
            err = fmax(err, fabs(c - r));
            mx = fmax(mx, fabs(r));
        }
    for (int a = 0; a < 3; a++)
        for (int b = a + 1; b < 3; b++) {
            if (tf[b] < tf[a]) { double x = tf[a]; tf[a] = tf[b]; tf[b] = x; }
            if (tr[b] < tr[a]) { double x = tr[a]; tr[a] = tr[b]; tr[b] = x; }
        }
    double rel = err / mx, limit = f64 ? 1e-11 : 1e-3;   /* far above any plan's error, far below a wrong result */
    int ok = rel < limit;
    failures += !ok;
    printf("%s n=%-5zu ld=%-5zu budget %-4g plan %-18s fmm %8.4f s  Accelerate %8.4f s  speedup %5.2f  "
           "rel. difference %.2e  %s\n",
           f64 ? "f64" : "f32", n, ld, g, plan, tf[1], tr[1], tr[1] / tf[1], rel, ok ? "ok" : "WRONG");
    fflush(stdout);
    free(A); free(B); free(C); free(R);
}

int main(int argc, char **argv) {
    size_t sizes[16] = {1000, 2048, 3000, 4096, 8192};
    int ns = 5;
    if (argc > 1) {
        ns = 0;
        for (int i = 1; i < argc && ns < 16; i++) sizes[ns++] = (size_t)atol(argv[i]);
    }
    for (int f64 = 0; f64 < 2; f64++) {
        for (int i = 0; i < ns; i++) run(sizes[i], sizes[i], f64, 0);
        run(4096, 4096 + 64, f64, 0);          /* leading dimensions larger than n */
        run(8192, 8192, f64, 4);               /* an error budget */
    }
    fmm_release();
    printf("%s\n", failures ? "FAILED" : "all ok");
    return failures != 0;
}
