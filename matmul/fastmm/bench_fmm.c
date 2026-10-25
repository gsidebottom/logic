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
 *   plan=...   any plan: fused levels from the top (SW, D48, SW2) ending in a leaf (G = one
 *              GEMM, B2/B4/B8 = classical blocked), e.g. plan=SW/D48/G
 *   auto       the plan the calibrated cost model picks for n (any n: padded to a size the
 *              plan's levels divide when that pays); auto:g the fastest plan whose error grows
 *              at most g-fold over the classical GEMM's (FMM_MAX_GROWTH=g for auto)
 *   M@k        method M with the GEMMs of its lowest level as k single-threaded streams taking
 *              products in turn (leaf Gk in a plan; G alone = Accelerate's own threading, one
 *              product at a time)
 * A fused pass streams once over its input and output blocks with the scheme's linear program
 * evaluated per element position in registers (kernels.h, from gen_kernels.py).
 *
 * The cost model: a fused level costs its three passes plus r times its sub-plan at n/g, a GEMM
 * leaf its time inside the level above it (or alone, on top); measured once per machine and
 * precision and cached in results/calib_f32.txt, calib_f64.txt (FMM_CALIB_DIR to move them,
 * FMM_RECALIB=1 to remeasure).  The planner, the executor and the calibration are the library's
 * (fmm.c, fmm_impl.h); this file adds the benchmark driver.  Every plan method prints its predicted time next to the
 * measured one.
 *
 * Repetitions are interleaved (each round runs every method once) and the median is reported.
 *
 *   bench_fmm -n N [-t f|d] [-m m1,m2,...] [-r reps]
 *   bench_fmm -n N [-t f|d] -p        calibrate for N, print the planner's choice per size
 *   bench_fmm -n N [-t f|d] -G        block GEMM time alone, back to back, and inside a D48 level
 */
#include "fmm.c"

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

/* R = A B (n x n, row-major) with every entry a compensated dot product (Ogita, Rump and Oishi's
 * Dot2: each product split exactly by an FMA, the sum accumulated with an error-free TwoSum),
 * as accurate as the product in twice the precision, then rounded to double: the f64 reference
 * for FMM_EXACT.  Blocks of 16 rows by 256 columns reuse each row of B across 16 rows of A. */
static void dd_gemm(size_t n, const double *A, const double *B, double *R) {
    enum { IB = 16, JB = 256 };
    dispatch_apply((n + IB - 1) / IB, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t bi) {
        double *s = malloc(IB * JB * sizeof(double)), *c = malloc(IB * JB * sizeof(double));
        size_t i0 = bi * IB, i1 = i0 + IB < n ? i0 + IB : n;
        for (size_t j0 = 0; j0 < n; j0 += JB) {
            size_t w = j0 + JB < n ? JB : n - j0;
            memset(s, 0, IB * JB * sizeof(double));
            memset(c, 0, IB * JB * sizeof(double));
            for (size_t k = 0; k < n; k++) {
                const double *restrict b = B + k * n + j0;
                for (size_t i = i0; i < i1; i++) {
                    const double a = A[i * n + k];
                    double *restrict si = s + (i - i0) * JB, *restrict ci = c + (i - i0) * JB;
                    for (size_t j = 0; j < w; j++) {
                        const double p = a * b[j], e = fma(a, b[j], -p);
                        const double t = si[j] + p, z = t - si[j];
                        ci[j] += ((si[j] - (t - z)) + (p - z)) + e;
                        si[j] = t;
                    }
                }
            }
            for (size_t i = i0; i < i1; i++)
                for (size_t j = 0; j < w; j++) R[i * n + j0 + j] = s[(i - i0) * JB + j] + c[(i - i0) * JB + j];
        }
        free(s);
        free(c);
    });
}

/* a benchmarked method: a plan, or (is_plan 0) the 48-scheme's program op by op */
typedef struct {
    const char *name;
    int plan[PLAN_MAX], is_plan;
    size_t npad;                    /* the size the plan runs at (n, or padded) */
    double pred, perr;
} meth_t;

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
    int reps = 3, table = 0;
    setenv("FMM_CALIB_DIR", "results", 0);  /* the benchmark's calibration lives with its results */
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-p")) table = 1;
        else if (!strcmp(argv[i], "-G")) table = 2;
        else if (i + 1 == argc) break;
        else if (!strcmp(argv[i], "-n")) n = (size_t)atol(argv[++i]);
        else if (!strcmp(argv[i], "-t")) type = argv[++i][0];
        else if (!strcmp(argv[i], "-m")) methods = argv[++i];
        else if (!strcmp(argv[i], "-r")) reps = atoi(argv[++i]);
    }
    if (n < 32 || reps < 1 || reps > 32) {
        fprintf(stderr, "n must be at least 32, reps 1..32\n");
        return 1;
    }
    if (table == 2) {
        if (type == 'f') gemm_probef(n);
        else gemm_probed(n);
    } else if (table) {
        if (type == 'f') plan_tablef(n);
        else plan_tabled(n);
    } else if (type == 'f') benchf(n, methods, reps);
    else benchd(n, methods, reps);
    return 0;
}
