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
 *   auto       the plan the calibrated cost model picks for n
 * A fused pass streams once over its input and output blocks with the scheme's linear program
 * evaluated per element position in registers (kernels.h, from gen_kernels.py).
 *
 * The cost model: a fused level costs its three passes plus r times its sub-plan at n/g, a GEMM
 * leaf its time inside the level above it (or alone, on top); measured once per machine and
 * precision and cached in results/calib_f32.txt, calib_f64.txt (FMM_CALIB_DIR to move them,
 * FMM_RECALIB=1 to remeasure).  Every plan method prints its predicted time next to the
 * measured one.
 *
 * Repetitions are interleaved (each round runs every method once) and the median is reported.
 *
 *   bench_fmm -n N [-t f|d] [-m m1,m2,...] [-r reps]
 *   bench_fmm -n N [-t f|d] -p        calibrate for N, print the planner's choice per size
 *   bench_fmm -n N [-t f|d] -G        block GEMM time alone, back to back, and inside a D48 level
 */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <dispatch/dispatch.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/sysctl.h>
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

/* the smallest block size the planner considers (FMM_MINB, default 256) */
static size_t fmm_minb(void) {
    const char *e = getenv("FMM_MINB");
    return e ? (size_t)atol(e) : 256;
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

/* write 128 MB from every core: the next timed run starts with cold caches in both clusters,
 * as a sub-product does inside a plan (its factors were written long before) */
static void evict(void) {
    static unsigned char *buf;
    static unsigned char val;
    size_t len = (size_t)128 << 20, chunks = 64, step = len / chunks;
    if (!buf) buf = alloc_t(len);
    val++;
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
        memset(buf + ch * step, val, step);
    });
}

/* ---- plans: fused levels from the top, ending in a leaf -------------------------------- */
/* leaves: G = one GEMM; B2, B4, B8 = classical as g^3 block GEMMs of n/g accumulating into C.
 * fused levels: SW = Strassen-Winograd <2x2x2:7>, D48 = our <4x4x4:48>, SW2 = Strassen^2
 * <4x4x4:49>.  NONE (calibration only) skips the products, leaving a level's passes. */
enum { LV_NONE = -1, LV_G = 0, LV_B2, LV_B4, LV_B8, LV_SW, LV_D48, LV_SW2, LV_N };
static const char *LV_NAME[LV_N] = {"G", "B2", "B4", "B8", "SW", "D48", "SW2"};
#define PLAN_MAX 16
static int lv_leaf(int lv) { return lv <= LV_B8; }
static int lv_grid(int lv) {
    static const int g[LV_N] = {1, 2, 4, 8, 2, 4, 4};
    return lv < 0 ? 1 : g[lv];
}
static int lv_rank(int lv) { return lv == LV_SW ? 7 : lv == LV_D48 ? 48 : 49; }

/* scratch elements a plan needs at size n: each fused level 3 r blocks of m*m + pad (S, T, M);
 * the levels below reuse their scratch product after product */
static size_t plan_work(const int *plan, size_t n) {
    if (lv_leaf(plan[0])) return 0;
    size_t m = n / lv_grid(plan[0]);
    return (size_t)3 * lv_rank(plan[0]) * (m * m + fmm_pad()) + plan_work(plan + 1, m);
}

static void plan_str(const int *plan, char *buf, size_t len) {
    buf[0] = 0;
    for (int i = 0; i < PLAN_MAX; i++) {
        strncat(buf, plan[i] < 0 ? "NONE" : LV_NAME[plan[i]], len - strlen(buf) - 1);
        if (lv_leaf(plan[i])) break;
        strncat(buf, "/", len - strlen(buf) - 1);
    }
}

/* the named methods as plans, or "plan=D48/SW/G"; 0 if the method is not a plan or the plan
 * does not divide n */
static int parse_plan(const char *meth, size_t n, int *plan) {
    static const struct { const char *name, *levels; } NAMED[] = {
        {"classical", "G"},        {"blk2", "B2"},         {"blk4", "B4"},
        {"blk8", "B8"},            {"sw1", "SW/G"},        {"sw2rec", "SW/SW/G"},
        {"sw3rec", "SW/SW/SW/G"},  {"sw4rec", "SW/SW/SW/SW/G"},
        {"sw2", "SW2/G"},          {"sw2sw", "SW2/SW/G"},  {"dps48", "D48/G"},
        {"dps48sw", "D48/SW/G"},   {"dps48x2", "D48/D48/G"},
    };
    const char *lv = NULL;
    for (size_t i = 0; i < sizeof NAMED / sizeof NAMED[0]; i++)
        if (!strcmp(meth, NAMED[i].name)) lv = NAMED[i].levels;
    if (!lv && !strncmp(meth, "plan=", 5)) lv = meth + 5;
    if (!lv) return 0;
    char buf[128];
    strncpy(buf, lv, sizeof buf - 1);
    buf[sizeof buf - 1] = 0;
    int k = 0;
    size_t sz = n;
    char *save = NULL;
    for (char *t = strtok_r(buf, "/", &save); t && k < PLAN_MAX; t = strtok_r(NULL, "/", &save)) {
        int found = -1;
        for (int j = 0; j < LV_N; j++)
            if (!strcmp(t, LV_NAME[j])) found = j;
        if (found < 0 || sz % lv_grid(found)) return 0;
        plan[k++] = found;
        sz /= lv_grid(found);
        if (lv_leaf(found)) return 1;
    }
    return 0;
}

/* ---- calibration and the planner ------------------------------------------------------- */
/* measured seconds per (kind, m).  A plan's top leaf alone: G m = one GEMM of size m, B2 m =
 * classical blocked 2x2 at size m (one call each, cold caches).  A fused level whose blocks have
 * size m: SW m, D48 m = its three passes; GSW m, GD48 m = its GEMM time per product (r GEMMs back
 * to back: below about 1 ms a GEMM in such a stream takes 13-27% longer than one alone) */
#define K_GIN 100   /* K_GIN + level: GEMM per product inside that level */
#define CALIB_FORMAT 2
#define CALIB_MAX 512
typedef struct {
    int kind[CALIB_MAX], n;
    size_t m[CALIB_MAX];
    double t[CALIB_MAX];
} calib_t;

static const char *kind_name(int kind) {
    static char buf[4][16];
    static int k;
    if (kind < K_GIN) return LV_NAME[kind];
    k = (k + 1) % 4;
    snprintf(buf[k], sizeof buf[k], "G%s", LV_NAME[kind - K_GIN]);
    return buf[k];
}

static int kind_parse(const char *s) {
    for (int v = 0; v < LV_N; v++) {
        if (!strcmp(s, LV_NAME[v])) return v;
        if (s[0] == 'G' && !strcmp(s + 1, LV_NAME[v])) return K_GIN + v;
    }
    return -1;
}

static double calib_get(const calib_t *c, int kind, size_t m) {
    for (int i = 0; i < c->n; i++)
        if (c->kind[i] == kind && c->m[i] == m) return c->t[i];
    return -1;
}

static void calib_put(calib_t *c, int kind, size_t m, double t) {
    for (int i = 0; i < c->n; i++)
        if (c->kind[i] == kind && c->m[i] == m) { c->t[i] = t; return; }
    if (c->n == CALIB_MAX) return;
    c->kind[c->n] = kind;
    c->m[c->n] = m;
    c->t[c->n++] = t;
}

/* the entries plan_best needs for n (t = 0 placeholders): the leaves alone at n, and for each
 * fused level its passes and per-product GEMM at blocks n/g, and the needs of n/g */
static void calib_need(calib_t *need, size_t n) {
    calib_put(need, LV_G, n, 0);
    if (n % 2 == 0 && n / 2 >= fmm_minb()) calib_put(need, LV_B2, n, 0);
    for (int lv = LV_SW; lv <= LV_D48; lv++) {
        size_t g = lv_grid(lv);
        if (n % g || n / g < fmm_minb()) continue;
        calib_put(need, lv, n / g, 0);
        calib_put(need, K_GIN + lv, n / g, 0);
        calib_need(need, n / g);
    }
}

static const char *machine(void) {
    static char buf[128];
    size_t len = sizeof buf;
    if (!buf[0] && sysctlbyname("machdep.cpu.brand_string", buf, &len, NULL, 0) != 0)
        strcpy(buf, "unknown");
    return buf;
}

static void calib_path(char *buf, size_t len, int f64) {
    const char *dir = getenv("FMM_CALIB_DIR");
    snprintf(buf, len, "%s/calib_%s.txt", dir ? dir : "results", f64 ? "f64" : "f32");
}

/* the cache, if it was measured on this machine with this padding and format */
static void calib_load(calib_t *c, int f64) {
    char path[256], line[256], kind[16];
    memset(c, 0, sizeof *c);
    const char *re = getenv("FMM_RECALIB");
    if (re && atoi(re)) return;
    calib_path(path, sizeof path, f64);
    FILE *f = fopen(path, "r");
    if (!f) return;
    int ok_machine = 0, ok_pad = 0, ok_format = 0;
    size_t m;
    double t;
    while (fgets(line, sizeof line, f)) {
        line[strcspn(line, "\n")] = 0;
        if (!strncmp(line, "# machine ", 10)) ok_machine = !strcmp(line + 10, machine());
        else if (!strncmp(line, "# pad ", 6)) ok_pad = (size_t)atol(line + 6) == fmm_pad();
        else if (!strncmp(line, "# format ", 9)) ok_format = atoi(line + 9) == CALIB_FORMAT;
        else if (line[0] != '#' && sscanf(line, "%15s %zu %lf", kind, &m, &t) == 3 && kind_parse(kind) >= 0)
            calib_put(c, kind_parse(kind), m, t);
    }
    fclose(f);
    if (!ok_machine || !ok_pad || !ok_format) {
        printf("# calibration %s is from another machine, padding or format: remeasuring\n", path);
        memset(c, 0, sizeof *c);
    }
}

static void calib_save(const calib_t *c, int f64) {
    char path[256];
    calib_path(path, sizeof path, f64);
    FILE *f = fopen(path, "w");
    if (!f) { perror(path); return; }
    fprintf(f, "# bench_fmm calibration, %s, seconds: G m = one GEMM of size m, B2 m = classical "
               "blocked 2x2 at size m (one call each); SW m, D48 m = the three passes of one such level "
               "with blocks of size m; GSW m, GD48 m = its GEMM time per product\n",
            f64 ? "f64" : "f32");
    fprintf(f, "# machine %s\n# pad %zu\n# format %d\n", machine(), fmm_pad(), CALIB_FORMAT);
    for (int v = 0; v < K_GIN + LV_N; v++)  /* by kind, then size */
        for (size_t m = 1; m < ((size_t)1 << 40); m *= 2)
            for (int i = 0; i < c->n; i++)
                if (c->kind[i] == v && c->m[i] >= m && c->m[i] < 2 * m)
                    fprintf(f, "%s %zu %.9f\n", kind_name(v), c->m[i], c->t[i]);
    fclose(f);
}

/* predicted seconds for a plan at size n below a fused level of type parent (-1: the top), -1
 * if the calibration lacks an entry it needs (B4, B8 and SW2 are not calibrated, B2 only on top) */
static double plan_cost_in(const calib_t *c, const int *plan, size_t n, int parent) {
    int lv = plan[0];
    if (lv == LV_G) return calib_get(c, parent < 0 ? LV_G : K_GIN + parent, n);
    if (lv == LV_B2) return parent < 0 ? calib_get(c, LV_B2, n) : -1;
    if (lv_leaf(lv)) return -1;
    size_t g = lv_grid(lv), m = n / g;
    if (n % g) return -1;
    double p = calib_get(c, lv, m), below = plan_cost_in(c, plan + 1, m, lv);
    return p < 0 || below < 0 ? -1 : p + lv_rank(lv) * below;
}

static double plan_cost(const calib_t *c, const int *plan, size_t n) { return plan_cost_in(c, plan, n, -1); }

/* the cheapest plan for n below a level of type parent (-1: the top) under the calibration:
 * dynamic programming over the first level, a leaf or a fused level over the cheapest plan for
 * n/g below it; -1 if nothing is calibrated */
static double plan_best_in(const calib_t *c, size_t n, int parent, int *plan) {
    double best = -1;
    for (int lv = LV_G; lv < LV_N; lv++) {
        /* SW2 has the passes of D48 and one product more: never cheaper */
        if (lv == LV_SW2 || lv == LV_B4 || lv == LV_B8) continue;
        int cand[PLAN_MAX] = {lv};
        double t;
        if (lv_leaf(lv)) {
            t = plan_cost_in(c, cand, n, parent);
        } else {
            size_t g = lv_grid(lv);
            if (n % g || n / g < fmm_minb()) continue;
            int sub[PLAN_MAX] = {0};
            double below = plan_best_in(c, n / g, lv, sub), p = calib_get(c, lv, n / g);
            memcpy(cand + 1, sub, (PLAN_MAX - 1) * sizeof(int));
            t = below < 0 || p < 0 ? -1 : p + lv_rank(lv) * below;
        }
        if (t >= 0 && (best < 0 || t < best)) {
            best = t;
            memcpy(plan, cand, sizeof cand);
        }
    }
    return best;
}

static double plan_best(const calib_t *c, size_t n, int *plan) { return plan_best_in(c, n, -1, plan); }

/* a benchmarked method: a plan, or (is_plan 0) the 48-scheme's program op by op */
typedef struct {
    const char *name;
    int plan[PLAN_MAX], is_plan;
    double pred;
} meth_t;

/* every plan for n down to blocks of fmm_minb() (fused levels SW and D48, any leaf) with its
 * predicted time, cheapest first; returns the count (at most max) */
typedef struct {
    int plan[PLAN_MAX];
    double t;
} ranked_t;

static void plan_enum_rec(const calib_t *c, size_t n0, size_t n, int *plan, int depth, ranked_t *out, int *cnt,
                          int max) {
    for (int lv = LV_G; lv < LV_N && *cnt < max; lv++) {
        if (lv == LV_SW2 || depth >= PLAN_MAX - 1) continue;
        plan[depth] = lv;
        if (lv_leaf(lv)) {
            double t = plan_cost(c, plan, n0);
            if (t > 0) {
                memcpy(out[*cnt].plan, plan, sizeof out[*cnt].plan);
                out[(*cnt)++].t = t;
            }
        } else if (n % lv_grid(lv) == 0 && n / lv_grid(lv) >= fmm_minb()) {
            plan_enum_rec(c, n0, n / lv_grid(lv), plan, depth + 1, out, cnt, max);
        }
    }
}

static int plan_enum(const calib_t *c, size_t n, ranked_t *out, int max) {
    int plan[PLAN_MAX] = {0}, cnt = 0;
    plan_enum_rec(c, n, n, plan, 0, out, &cnt, max);
    for (int a = 0; a < cnt; a++)
        for (int b = a + 1; b < cnt; b++)
            if (out[b].t < out[a].t) { ranked_t x = out[a]; out[a] = out[b]; out[b] = x; }
    return cnt;
}

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
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-p")) table = 1;
        else if (!strcmp(argv[i], "-G")) table = 2;
        else if (i + 1 == argc) break;
        else if (!strcmp(argv[i], "-n")) n = (size_t)atol(argv[++i]);
        else if (!strcmp(argv[i], "-t")) type = argv[++i][0];
        else if (!strcmp(argv[i], "-m")) methods = argv[++i];
        else if (!strcmp(argv[i], "-r")) reps = atoi(argv[++i]);
    }
    if (n % 32 || reps < 1 || reps > 32) {
        fprintf(stderr, "n must be a multiple of 32, reps 1..32\n");
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
