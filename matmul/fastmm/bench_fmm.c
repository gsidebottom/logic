/* bench_fmm.c: fast matrix multiplication schemes against classical GEMM on Apple silicon.
 *
 * Methods (row-major n x n, products on Accelerate's GEMM):
 *   classical  one GEMM
 *   blkG       classical as G^3 block GEMMs of size n/G (G = 2, 4, 8) accumulating into C
 *   sw1        Strassen-Winograd, one level (7 GEMMs of n/2), one fused pass per side
 *   sw2rec     Strassen-Winograd, two levels recursively (49 GEMMs of n/4), a pass per level
 *   sw3rec     three levels (343 GEMMs of n/8); sw4rec four levels (2,401 of n/16)
 *   sw2        Strassen-Winograd squared as one <4x4x4:49> level: one fused pass per side
 *   dps48      our <4x4x4:48> (201 operations) as one level: one fused pass per side
 *   dps48ops   the same program one block operation at a time (a pass per operation)
 *   dps48sw    hybrid: our 48 level on top, one Strassen level per product (336 GEMMs of n/8)
 *   sw2sw      Strassen^2 level on top, one Strassen level per product (343 GEMMs of n/8)
 *   dps48x2    two levels of our 48-scheme (2,304 GEMMs of n/16)
 * A fused pass streams once over its input and output blocks with the scheme's linear program
 * evaluated per element position in registers (kernels.h, from gen_kernels.py).
 *
 * Repetitions are interleaved (each round runs every method once) and the median is reported.
 *
 *   bench_fmm -n N [-t f|d] [-m m1,m2,...] [-r reps]
 */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <dispatch/dispatch.h>
#include <math.h>
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
    if (posix_memalign(&p, 16384, bytes ? bytes : 16) != 0) {
        perror("posix_memalign");
        exit(1);
    }
    return p;
}

/* extra elements between scratch blocks (FMM_PAD, default 1040: blocks of power-of-two size
 * would otherwise start at one offset modulo the cache's set span, and the 64 streams of a
 * fused 4x4 pass would fight over one set; measured 2.5x on the fused passes) */
static size_t fmm_pad(void) {
    const char *e = getenv("FMM_PAD");
    return e ? (size_t)atol(e) : 1040;
}

/* the largest temporary index used by the 48-scheme's programs */
static int max_temp(void) {
    int mx = 0;
    const int (*lists[3])[4] = {dps48_L_ops, dps48_R_ops, dps48_P_ops};
    int lens[3] = {dps48_L_ops_len, dps48_R_ops_len, dps48_P_ops_len};
    for (int l = 0; l < 3; l++)
        for (int q = 0; q < lens[l]; q++)
            for (int j = 0; j < 4; j += 2)
                if (lists[l][q][j] >= 100000 && lists[l][q][j] < 200000 && lists[l][q][j] - 100000 > mx)
                    mx = lists[l][q][j] - 100000;
    return mx;
}

/* how the products of a fused level are computed */
typedef enum { SUB_GEMM, SUB_SW1, SUB_DPS48 } sub_t;

#define T float
#define SUF f
#define GEMM cblas_sgemm
#include "bench_impl.h"
#undef T
#undef SUF
#undef GEMM
#define T double
#define SUF d
#define GEMM cblas_dgemm
#include "bench_impl.h"
#undef T
#undef SUF
#undef GEMM

int main(int argc, char **argv) {
    size_t n = 4096;
    char type = 'f';
    const char *methods = "classical,sw1,sw2rec,sw2,dps48,dps48ops";
    int reps = 3;
    for (int i = 1; i + 1 < argc; i += 2) {
        if (!strcmp(argv[i], "-n")) n = (size_t)atol(argv[i + 1]);
        else if (!strcmp(argv[i], "-t")) type = argv[i + 1][0];
        else if (!strcmp(argv[i], "-m")) methods = argv[i + 1];
        else if (!strcmp(argv[i], "-r")) reps = atoi(argv[i + 1]);
    }
    if (n % 32 || reps < 1 || reps > 32) {
        fprintf(stderr, "n must be a multiple of 32, reps 1..32\n");
        return 1;
    }
    if (type == 'f') benchf(n, methods, reps);
    else benchd(n, methods, reps);
    return 0;
}
