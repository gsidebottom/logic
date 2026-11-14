/* probe_strip.c: are the fused passes at the memory system's limit?  A plain three-stream pass
 * moves 208-220 GB/s on this machine (probe_nt) while a fused pass of 58-64 streams moves about
 * 130.  Here the library's own kernels run a level's pass over all cores (64 row chunks, as
 * fmm_impl.h's pass does) directly, or strip-mined: W elements of every input stream are copied
 * into a buffer in L1, the kernel runs on the buffers, and W elements of every output are copied
 * out, so that memory sees each stream in sequential bursts instead of 64 streams advancing a
 * few bytes at a time (no gain: 10-20% slower).  The passes that write most are the slowest (L: 16
 * blocks in, 48 out, 121 GB/s; P: 48 in, 16 out, 155), as if every written line were first read; so
 * also: the row cut into tiles of W elements, and before a tile is computed its output lines are
 * claimed with DC ZVA, which zeroes a 64-byte line without reading it ("zva"; "tiled" is the same
 * without the claims).  Prints GB/s of the words the pass moves.
 *   probe_strip [-t f|d] [-n 6912] [-s 2]        (n: the problem; every kernel on its own block grid) */
#include <dispatch/dispatch.h>
#include <stdint.h>
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
    if (posix_memalign(&p, 16384, bytes)) exit(1);
    memset(p, 0, bytes);
    return p;
}
#define PAD 1040
typedef void (*kd_t)(size_t, size_t, size_t, const double *const *, double *const *, size_t, size_t);
typedef void (*kf_t)(size_t, size_t, size_t, const float *const *, float *const *, size_t, size_t);

/* one pass: nin blocks of rows x cols (leading dimension ldi) into nout blocks (ldo); W = 0 direct,
 * else strip-mined with W elements per burst; which: 1 inputs buffered, 2 outputs, 3 both */
static double run(int f64, void *kern, int nin, int nout, size_t rows, size_t cols, size_t ldi, size_t ldo,
                  void *const *in, void *const *out, size_t W, int which, double secs) {
    size_t es = f64 ? 8 : 4, chunks = 64, step = (rows + chunks - 1) / chunks;
    int reps = 0;
    double t0 = now();
    while (now() - t0 < secs) {
        dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
            size_t r0 = ch * step, r1 = r0 + step < rows ? r0 + step : rows;
            if (r0 >= r1) return;
            if (!W) {
                if (f64) ((kd_t)kern)(cols, ldi, ldo, (const double *const *)in, (double *const *)out, r0, r1);
                else ((kf_t)kern)(cols, ldi, ldo, (const float *const *)in, (float *const *)out, r0, r1);
                return;
            }
            char *buf = NULL;
            if (posix_memalign((void **)&buf, 16384, (size_t)(nin + nout) * (W * es + 64))) exit(1);
            void *bi[256], *bo[256];
            for (int i = 0; i < nin; i++) bi[i] = buf + (size_t)i * (W * es + 64);
            for (int q = 0; q < nout; q++) bo[q] = buf + (size_t)(nin + q) * (W * es + 64);
            void *pi[256], *po[256];
            for (size_t r = r0; r < r1; r++)
                for (size_t c0 = 0; c0 < cols; c0 += W) {
                    size_t w = c0 + W < cols ? W : cols - c0;
                    for (int i = 0; i < nin; i++) {
                        char *src = (char *)in[i] + (r * ldi + c0) * es;
                        if (which & 1) { memcpy(bi[i], src, w * es); pi[i] = bi[i]; } else pi[i] = src;
                    }
                    for (int q = 0; q < nout; q++) po[q] = which & 2 ? bo[q] : (char *)out[q] + (r * ldo + c0) * es;
                    if (which & 4)      /* claim the output lines without reading them: DC ZVA zeroes a 64-byte line */
                        for (int q = 0; q < nout; q++) {
                            uintptr_t lo = ((uintptr_t)po[q] + 63) & ~(uintptr_t)63, hi = ((uintptr_t)po[q] + w * es) & ~(uintptr_t)63;
                            for (uintptr_t x = lo; x < hi; x += 64) __asm__ volatile("dc zva, %0" : : "r"(x) : "memory");
                        }
                    if (f64) ((kd_t)kern)(w, 0, 0, (const double *const *)pi, (double *const *)po, 0, 1);
                    else ((kf_t)kern)(w, 0, 0, (const float *const *)pi, (float *const *)po, 0, 1);
                    if (which & 2)
                        for (int q = 0; q < nout; q++) memcpy((char *)out[q] + (r * ldo + c0) * es, bo[q], w * es);
                }
            free(buf);
        });
        reps++;
    }
    double t = now() - t0;
    return (double)reps * (nin + nout) * rows * cols * es / t / 1e9;
}

int main(int argc, char **argv) {
    int f64 = 1;
    size_t n = 6912;
    double secs = 2;
    for (int i = 1; i + 1 < argc; i += 2) {
        if (!strcmp(argv[i], "-t")) f64 = argv[i + 1][0] == 'd';
        else if (!strcmp(argv[i], "-n")) n = (size_t)atol(argv[i + 1]);
        else if (!strcmp(argv[i], "-s")) secs = atof(argv[i + 1]);
    }
    size_t es = f64 ? 8 : 4;
    struct { const char *name; void *kd, *kf; int g1, g2, nout, isP; } K[] = {
        {"D48 L  16 -> 48", dps48_L_d, dps48_L_f, 4, 4, 48, 0}, {"D48 P  48 -> 16", dps48_P_d, dps48_P_f, 4, 4, 48, 1},
        {"R363 L  18 -> 40", r363_L_d, r363_L_f, 3, 6, 40, 0}, {"R363 P  40 -> 9", r363_P_d, r363_P_f, 3, 3, 40, 1},
        {"SW L    4 -> 7", sw_L_d, sw_L_f, 2, 2, 7, 0},
    };
    char *big = alloc_t(n * n * es);
    for (int v = 0; v < (int)(sizeof K / sizeof K[0]); v++) {
        int g1 = K[v].g1, g2 = K[v].g2, r = K[v].nout, nb = g1 * g2;
        size_t rows = n / g1, cols = n / g2, bs = (rows * cols + PAD) * es;
        char *scr = alloc_t((size_t)r * bs);
        void *blk[64], *sc[64];
        for (int q = 0; q < nb; q++) blk[q] = big + ((size_t)(q / g2) * rows * n + (size_t)(q % g2) * cols) * es;
        for (int q = 0; q < r; q++) sc[q] = scr + (size_t)q * bs;
        int nin = K[v].isP ? r : nb, nout = K[v].isP ? nb : r;
        void *const *in = K[v].isP ? sc : blk, *const *out = K[v].isP ? blk : sc;
        size_t ldi = K[v].isP ? cols : n, ldo = K[v].isP ? n : cols;
        void *kern = f64 ? K[v].kd : K[v].kf;
        printf("%s %-17s n=%zu  direct %6.1f GB/s |", f64 ? "f64" : "f32", K[v].name, n,
               run(f64, kern, nin, nout, rows, cols, ldi, ldo, in, out, 0, 0, secs));
        static const size_t WS[] = {64, 128, 256, 512, 1024};
        for (int w = 0; w < 5; w++)
            printf("  W=%zu: tiled %6.1f zva %6.1f", WS[w],
                   run(f64, kern, nin, nout, rows, cols, ldi, ldo, in, out, WS[w], 0, secs),
                   run(f64, kern, nin, nout, rows, cols, ldi, ldo, in, out, WS[w], 4, secs));
        printf("\n");
        fflush(stdout);
        free(scr);
    }
    return 0;
}
