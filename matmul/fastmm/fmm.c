/* fmm.c: fast matrix multiplication on Apple silicon (fmm.h), and the core of bench_fmm.
 *
 * A plan is a sequence of fused levels from the top -- SW (Strassen-Winograd <2x2x2:7>), D48
 * (the rank-48 <4x4x4:48> scheme of Dumas, Pernet and Sedoglavic, as their 262-operation
 * accurate program; see
 * gen_kernels.py), SW2 (Strassen^2) -- ending in a leaf: G (one GEMM, Accelerate), its products
 * as k single-threaded GEMM streams (Gk) or with NEON products (GkNj), or classical blocked
 * (B2/B4/B8).  A fused level streams once over its input and output blocks with the scheme's
 * linear program evaluated per element position in registers (kernels.h, from gen_kernels.py);
 * a level over a level over GEMM streams can pipeline its sub-problems (X+p: their passes on p
 * threads while the GEMMs run), two such levels nest (X+/Z+p/...).
 *
 * The planner: a level costs its passes plus r times its sub-plan at n/g, a GEMM leaf its time
 * inside the level above it (or alone, on top), a pipelined level its passes plus r times the
 * steady time per sub-problem plus fill and drain; all measured once per machine and precision
 * (the calibration) and cached; dynamic programming picks the cheapest plan, optionally within
 * an error-growth budget (a per-level error model measured with the calibration).
 */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#include <dispatch/dispatch.h>
#include <ctype.h>
#include <errno.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/sysctl.h>
#include <time.h>

#include "fmm.h"
#include "kernels.h"
#include "neon_gemm.h"

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

/* the f64 passes of the f32 path (FMM_F64PASS=1): the 4x4 scheme's passes read and write float
 * blocks but add in double, so a pass rounds only where it stores a block for the GEMM or the
 * output, once per element, instead of at every addition; the GEMMs are unchanged */
static int fmm_f64pass(void) {
    static int v = -1;
    if (v < 0) {
        const char *e = getenv("FMM_F64PASS");
        v = e && atoi(e) > 0;
    }
    return v;
}

/* the smallest block size the planner considers (FMM_MINB, default 256) */
static size_t fmm_minb(void) {
    const char *e = getenv("FMM_MINB");
    return e ? (size_t)atol(e) : 256;
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
 * <4x4x4:49>.  NONE (calibration only) skips the products, leaving a level's passes.  A plan
 * entry is a level code; the G leaf below a fused level may add k << 8 (written Gk): the
 * level's products as k single-threaded GEMM streams taking products in turn.  Plain G runs
 * them one at a time with Accelerate's own threading, which drives each SME unit (one per
 * cluster) from one thread; two or three threads per unit keep it busier.  Adding j << 16
 * (written GkNj) gives the level's last j products to NEON GEMMs on fmm_neon_threads() more
 * cores, in row slabs, while the streams take the others.  A fused level whose sub-plan is a
 * fused level over a G leaf may add 1 << 24 (written with +, e.g. D48+/D48/G6): its products
 * are pipelined, the passes of the neighbouring products on fmm_pass_threads() cores (or on
 * p cores, with p << 25, written D48+p) while the GEMMs of one product run. */
enum { LV_NONE = -1, LV_G = 0, LV_B2, LV_B4, LV_B8, LV_SW, LV_D48, LV_SW2, LV_R336, LV_R363, LV_R633,
       LV_T336, LV_T363, LV_T633, LV_N };
static const char *LV_NAME[LV_N] = {"G", "B2", "B4", "B8", "SW", "D48", "SW2", "R336", "R363", "R633", "T336", "T363", "T633"};
/* a level's grid g1 x g2 x g3 (A split into g1 x g2 blocks, B into g2 x g3, C into g1 x g3) and
 * its rank; the R levels are the three orientations of the accurate <3x3x6:40> scheme of
 * Dumas, Pernet and Sedoglavic (PLinOpt's 3x3x6_40_DPS-accurate and transposes; schemes/); the T
 * levels the three orientations of the ternary <3x3x6:42> scheme 3x3x6_m42_cr139 of Perminov's
 * catalogue (coefficients 0, +-1, 139 additions in its three programs: cheap passes, two products
 * more and about 2.8x the amplification of the R levels), available to named plans as a trial */
typedef struct { int g1, g2, g3, r; } lvdef_t;
static const lvdef_t LVDEF[LV_N] = {{1, 1, 1, 1},  {2, 2, 2, 8},  {4, 4, 4, 64}, {8, 8, 8, 512}, {2, 2, 2, 7},
                                    {4, 4, 4, 48}, {4, 4, 4, 49}, {3, 3, 6, 40}, {3, 6, 3, 40},  {6, 3, 3, 40},
                                    {3, 3, 6, 42}, {3, 6, 3, 42}, {6, 3, 3, 42}};
/* the fused levels the planner uses (SW2 has D48's passes and one product more; the T levels are
 * not in the menu: named plans only, until the trial says they pay) */
static const int FUSED[] = {LV_SW, LV_D48, LV_R336, LV_R363, LV_R633};
#define NFUSED ((int)(sizeof FUSED / sizeof FUSED[0]))
/* the shape of a product: (m x k) (k x n); a level divides it by its grid */
typedef struct { size_t m, k, n; } shape_t;
static shape_t sq(size_t n) { shape_t s = {n, n, n}; return s; }
static int shape_sq(shape_t s) { return s.m == s.k && s.k == s.n; }
static int shape_eq(shape_t a, shape_t b) { return a.m == b.m && a.k == b.k && a.n == b.n; }
static size_t shape_min(shape_t s) { size_t x = s.m < s.k ? s.m : s.k; return x < s.n ? x : s.n; }
static int lv_divides(int lv, shape_t s) {
    return s.m % LVDEF[lv].g1 == 0 && s.k % LVDEF[lv].g2 == 0 && s.n % LVDEF[lv].g3 == 0;
}
static shape_t lv_sub(int lv, shape_t s) {     /* the shape of the level's products */
    shape_t t = {s.m / LVDEF[lv].g1, s.k / LVDEF[lv].g2, s.n / LVDEF[lv].g3};
    return t;
}
static shape_t lv_up(int lv, shape_t t) {      /* the problem whose products have shape t */
    shape_t s = {t.m * LVDEF[lv].g1, t.k * LVDEF[lv].g2, t.n * LVDEF[lv].g3};
    return s;
}
#define PLAN_MAX 16
#define PLV(e) ((e) < 0 ? (e) : (e) & 0xff)     /* the level code of a plan entry */
#define PST(e) ((e) < 0 ? 0 : ((e) >> 8) & 0xff)  /* its GEMM streams */
#define PNE(e) ((e) < 0 ? 0 : ((e) >> 16) & 0xff) /* its products on NEON */
#define PPI(e) ((e) < 0 ? 0 : ((e) >> 24) & 1)    /* its sub-problems pipelined */
#define PPW(e) ((e) < 0 ? 0 : ((e) >> 25) & 0xf)  /* on this many pass threads (0: the default) */
static const int STREAMS[] = {0, 3, 4, 6};       /* the stream counts the planner considers */
#define NSTREAMS ((int)(sizeof STREAMS / sizeof STREAMS[0]))
static int lv_leaf(int lv) { return lv <= LV_B8; }

/* pass threads beside the GEMM streams of a pipelined level (FMM_PASS_THREADS, default 2) */
static int fmm_pass_threads(void) {
    const char *e = getenv("FMM_PASS_THREADS");
    return e ? atoi(e) : 2;
}

/* NEON GEMM threads beside the streams of a GkNj leaf (FMM_NEON_THREADS, default 4) */
static int fmm_neon_threads(void) {
    const char *e = getenv("FMM_NEON_THREADS");
    return e ? atoi(e) : 4;
}
static int lv_grid(int lv) { return lv < 0 ? 1 : LVDEF[lv].g1; }     /* the square leaves' grid */
static int lv_rank(int lv) { return LVDEF[lv].r; }

/* scratch elements a plan needs on a problem of shape s: each fused level r blocks of each of its
 * three block shapes, pad apart (S, T, M); the levels below reuse their scratch product after
 * product */
static size_t plan_work(const int *plan, shape_t s) {
    int lv = PLV(plan[0]);
    if (lv_leaf(lv)) return 0;
    shape_t t = lv_sub(lv, s);
    size_t pad = fmm_pad(), blocks = (size_t)lv_rank(lv) * ((t.m * t.k + pad) + (t.k * t.n + pad) + (t.m * t.n + pad));
    /* a pipelined level double-buffers the scratch of the level below */
    return blocks + (PPI(plan[0]) ? 2 : 1) * plan_work(plan + 1, t);
}

static void plan_str(const int *plan, char *buf, size_t len) {
    buf[0] = 0;
    for (int i = 0; i < PLAN_MAX; i++) {
        int lv = PLV(plan[i]);
        char e[16];
        if (PNE(plan[i])) snprintf(e, sizeof e, "%s%dN%d", LV_NAME[lv], PST(plan[i]), PNE(plan[i]));
        else if (PST(plan[i])) snprintf(e, sizeof e, "%s%d", LV_NAME[lv], PST(plan[i]));
        else if (PPW(plan[i])) snprintf(e, sizeof e, "%s+%d", LV_NAME[lv], PPW(plan[i]));
        else snprintf(e, sizeof e, "%s%s", lv < 0 ? "NONE" : LV_NAME[lv], PPI(plan[i]) ? "+" : "");
        strncat(buf, e, len - strlen(buf) - 1);
        if (lv_leaf(lv)) break;
        strncat(buf, "/", len - strlen(buf) - 1);
    }
}

/* the named methods as plans, or "plan=D48/SW/G3"; a suffix @k gives the plan's G leaf k
 * streams; 0 if the method is not a plan or the plan does not divide the shape */
static int parse_plan(const char *meth, shape_t n, int *plan) {
    static const struct { const char *name, *levels; } NAMED[] = {
        {"classical", "G"},        {"blk2", "B2"},         {"blk4", "B4"},
        {"blk8", "B8"},            {"sw1", "SW/G"},        {"sw2rec", "SW/SW/G"},
        {"sw3rec", "SW/SW/SW/G"},  {"sw4rec", "SW/SW/SW/SW/G"},
        {"sw2", "SW2/G"},          {"sw2sw", "SW2/SW/G"},  {"dps48", "D48/G"},
        {"dps48sw", "D48/SW/G"},   {"dps48x2", "D48/D48/G"},
        {"r336", "R336/G"},        {"r363", "R363/G"},     {"r633", "R633/G"},
        {"r336x2", "R336/R363/G"}, {"r336x3", "R336/R363/R633/G"},
        {"swr336", "SW/R336/G"},   {"r336sw", "R336/SW/G"},
    };
    char name[128], buf[128];
    strncpy(name, meth, sizeof name - 1);
    name[sizeof name - 1] = 0;
    char *at = strchr(name, '@');
    int streams = at ? atoi(at + 1) : -1;
    if (at) *at = 0;
    const char *lv = NULL;
    for (size_t i = 0; i < sizeof NAMED / sizeof NAMED[0]; i++)
        if (!strcmp(name, NAMED[i].name)) lv = NAMED[i].levels;
    if (!lv && !strncmp(name, "plan=", 5)) lv = name + 5;
    if (!lv) return 0;
    strncpy(buf, lv, sizeof buf - 1);
    buf[sizeof buf - 1] = 0;
    int k = 0;
    shape_t sz = n;
    char *save = NULL;
    for (char *t = strtok_r(buf, "/", &save); t && k < PLAN_MAX; t = strtok_r(NULL, "/", &save)) {
        int found = -1, st = 0, ne = 0, pipe = 0, pw = 0;
        char *plus = strchr(t, '+');
        if (plus && plus > t) {
            pipe = 1;
            pw = atoi(plus + 1);
            *plus = 0;
        }
        for (int j = 0; j < LV_N; j++)
            if (!strcmp(t, LV_NAME[j])) found = j;
        if (found < 0 && t[0] == 'G' && isdigit((unsigned char)t[1])) {
            found = LV_G;
            char *rest;
            st = (int)strtol(t + 1, &rest, 10);
            if (*rest == 'N') ne = atoi(rest + 1);
        }
        if (found < 0 || !lv_divides(found, sz)) return 0;
        sz = lv_sub(found, sz);
        if (found == LV_G && streams >= 0 && k > 0) st = streams;
        if ((st || ne) && k == 0) return 0;     /* streams need a level whose products they share */
        if (ne && !st) return 0;
        if (pipe && lv_leaf(found)) return 0;
        plan[k++] = found | (st << 8) | (ne << 16) | (pipe << 24) | ((pw & 0xf) << 25);
        if (lv_leaf(found)) return 1;
    }
    return 0;
}

/* ---- calibration and the planner ------------------------------------------------------- */
/* measured seconds per (kind, m).  A plan's top leaf alone: G m = one GEMM of size m, B2 m =
 * classical blocked 2x2 at size m (one call each, cold caches).  A fused level whose blocks have
 * size m: SW m, D48 m = its three passes; GSW m, GD48 m = its GEMM time per product run one at a
 * time (back to back: below about 1 ms a GEMM so takes 13-27% longer than alone), GkSW m, GkD48
 * m = the same with k streams.  Sub-problems of a pipelined level, each a level Y with blocks m
 * over k GEMM streams (3, 6) with p pass threads (2, 3, 4): PYkKpPs m = the steady time per sub-problem, PYkKpPo
 * m = the pipeline's fill and drain (a pipeline of q sub-problems takes q s + o) */
#define K_GIN 100   /* K_GIN + 16 k + level: GEMM per product inside that level, k streams */
#define K_PIPE 1000 /* K_PIPE + ((16 k + p) 2 + part) 16 + level: pipelined sub-problems */
#define K_ERR 9000  /* K_ERR + i: the error of ERR_PLANS[i] against the classical GEMM at n = N_E */
#define N_E 2304    /* divisible by 16 (D48/D48) and by 3 and 6 (the R levels); blocks of 384 and up */
#define NERR 6
static const char *ERR_PLANS[NERR] = {"sw1", "dps48", "dps48x2", "r336", "r363", "r633"};
static const char *ERR_NAMES[NERR] = {"ESW", "ED48", "ED48D48", "ER336", "ER363", "ER633"};
#define CALIB_FORMAT 5
static const int PIPE_K[] = {3, 6}, PIPE_P[] = {2, 3, 4};  /* the pipelines the planner considers */
#define NPIPE_K ((int)(sizeof PIPE_K / sizeof PIPE_K[0]))
#define NPIPE_P ((int)(sizeof PIPE_P / sizeof PIPE_P[0]))
/* the table's capacity: a square calibration to 13824 fills about 950 entries, each rectangular
 * shape calibrated for adds about 120 */
#define CALIB_MAX 4096
typedef struct {
    int kind[CALIB_MAX], n;
    shape_t s[CALIB_MAX];
    double t[CALIB_MAX];
} calib_t;

static int kind_gin(int lv, int streams) { return K_GIN + 16 * streams + lv; }
static int kind_pipe(int lv, int streams, int passes, int over) {
    return K_PIPE + ((16 * streams + passes) * 2 + over) * 16 + lv;
}

static const char *kind_name(int kind) {
    static char buf[4][24];
    static int k;
    if (kind < K_GIN) return LV_NAME[kind];
    k = (k + 1) % 4;
    if (kind >= K_ERR) return ERR_NAMES[kind - K_ERR];
    if (kind >= K_PIPE) {
        int x = kind - K_PIPE, lv = x % 16, over = (x / 16) % 2, sp = x / 32;
        snprintf(buf[k], sizeof buf[k], "P%sk%dp%d%c", LV_NAME[lv], sp / 16, sp % 16, over ? 'o' : 's');
        return buf[k];
    }
    int st = (kind - K_GIN) / 16, lv = (kind - K_GIN) % 16;
    if (st) snprintf(buf[k], sizeof buf[k], "G%d%s", st, LV_NAME[lv]);
    else snprintf(buf[k], sizeof buf[k], "G%s", LV_NAME[lv]);
    return buf[k];
}

static int kind_parse(const char *s) {
    for (int v = 0; v < LV_N; v++)
        if (!strcmp(s, LV_NAME[v])) return v;
    for (int i = 0; i < NERR; i++)
        if (!strcmp(s, ERR_NAMES[i])) return K_ERR + i;
    if (s[0] == 'P') {                      /* PD48k6p2s */
        const char *kp = strchr(s, 'k');
        if (!kp) return -1;
        char name[8] = {0};
        if (kp - s - 1 <= 0 || kp - s - 1 >= (int)sizeof name) return -1;
        memcpy(name, s + 1, (size_t)(kp - s - 1));
        int st, pw;
        char part;
        if (sscanf(kp, "k%dp%d%c", &st, &pw, &part) != 3 || (part != 's' && part != 'o')) return -1;
        for (int v = 0; v < LV_N; v++)
            if (!strcmp(name, LV_NAME[v])) return kind_pipe(v, st, pw, part == 'o');
        return -1;
    }
    if (s[0] != 'G') return -1;
    const char *p = s + 1;
    int st = 0;
    while (isdigit((unsigned char)*p)) st = 10 * st + (*p++ - '0');
    for (int v = 0; v < LV_N; v++)
        if (!strcmp(p, LV_NAME[v])) return kind_gin(v, st);
    return -1;
}

static double calib_get(const calib_t *c, int kind, shape_t s) {
    for (int i = 0; i < c->n; i++)
        if (c->kind[i] == kind && shape_eq(c->s[i], s)) return c->t[i];
    return -1;
}

/* the square size whose entry of this kind costs what a rectangular shape's would, for a shape
 * that was not measured: GEMM-like entries (a leaf, the GEMM per product, a pipeline's steady and
 * fill times) go by flops, cbrt(m k n) (Accelerate runs rectangular shapes within 5% of the square
 * rate), the passes of a level by their traffic, (g1 g2 + r) m k + (g2 g3 + r) k n + (g1 g3 + r) m n
 * words for its blocks of each operand against (g1 g2 + g2 g3 + g1 g3 + 3 r) m'^2 for a square m' */
static double shape_equiv(int kind, shape_t s) {
    if (shape_sq(s)) return (double)s.m;
    if (kind < K_GIN && !lv_leaf(kind)) {
        lvdef_t d = LVDEF[kind];
        double w = (d.g1 * d.g2 + d.r) * ((double)s.m * s.k) + (d.g2 * d.g3 + d.r) * ((double)s.k * s.n) +
                   (d.g1 * d.g3 + d.r) * ((double)s.m * s.n);
        return sqrt(w / (d.g1 * d.g2 + d.g2 * d.g3 + d.g1 * d.g3 + 3 * d.r));
    }
    return cbrt((double)s.m * s.k * s.n);
}

/* a cost-model entry at any shape: the measured value, else log-log interpolation between the
 * nearest measured square sizes below and above the shape's equivalent square size (times go like
 * m^3 for GEMMs and m^2 for passes, so a straight line in log-log; for a rectangular shape an
 * estimate, which fmm_calibrate_mkn replaces by measurements); -1 outside the measured range */
static double calib_cost(const calib_t *c, int kind, shape_t s) {
    double m = shape_equiv(kind, s), tlo = -1, thi = -1, teq = -1;
    size_t lo = 0, hi = 0;
    for (int i = 0; i < c->n; i++) {
        if (c->kind[i] != kind) continue;
        if (shape_eq(c->s[i], s)) return c->t[i];
        if (!shape_sq(c->s[i])) continue;
        size_t cm = c->s[i].m;
        if ((double)cm == m) { teq = c->t[i]; continue; }
        if ((double)cm < m && cm > lo) { lo = cm; tlo = c->t[i]; }
        if ((double)cm > m && (hi == 0 || cm < hi)) { hi = cm; thi = c->t[i]; }
    }
    if (teq >= 0) return teq;
    if (lo == 0 || hi == 0 || tlo <= 0 || thi <= 0) return -1;
    double x = log(m / (double)lo) / log((double)hi / (double)lo);
    return tlo * pow(thi / tlo, x);
}

static void calib_put(calib_t *c, int kind, shape_t s, double t) {
    for (int i = 0; i < c->n; i++)
        if (c->kind[i] == kind && shape_eq(c->s[i], s)) { c->t[i] = t; return; }
    if (c->n == CALIB_MAX) {                /* dropped: the planner then lacks it (and re-measures it) */
        static int warned;
        if (!warned++) fprintf(stderr, "fmm: calibration table full (%d entries), entries dropped\n", CALIB_MAX);
        return;
    }
    c->kind[c->n] = kind;
    c->s[c->n] = s;
    c->t[c->n++] = t;
}

/* the entries plan_best needs for a problem of shape s (t = 0 placeholders): the leaves alone
 * at s, and for each fused level dividing s its passes and per-product GEMM (every stream count)
 * at its product shape, and the needs of that shape; the error model once, for square problems
 * of N_E and up */
static void calib_need(calib_t *need, shape_t s) {
    if (shape_sq(s) && s.m >= N_E)
        for (int i = 0; i < NERR; i++) calib_put(need, K_ERR + i, sq(N_E), 0);
    calib_put(need, LV_G, s, 0);
    if (shape_sq(s) && s.m % 2 == 0 && s.m / 2 >= fmm_minb()) calib_put(need, LV_B2, s, 0);
    for (int f = 0; f < NFUSED; f++) {
        int lv = FUSED[f];
        if (!lv_divides(lv, s) || shape_min(lv_sub(lv, s)) < fmm_minb()) continue;
        shape_t t = lv_sub(lv, s);
        calib_put(need, lv, t, 0);
        for (int i = 0; i < NSTREAMS; i++) calib_put(need, kind_gin(lv, STREAMS[i]), t, 0);
        /* a pipelined level at s: its sub-problems are levels ly on products of shape t */
        for (int fy = 0; fy < NFUSED; fy++) {
            int ly = FUSED[fy];
            if (!lv_divides(ly, t) || shape_min(lv_sub(ly, t)) < fmm_minb()) continue;
            shape_t ty = lv_sub(ly, t);
            for (int a = 0; a < NPIPE_K; a++)
                for (int b = 0; b < NPIPE_P; b++)
                    for (int o = 0; o < 2; o++) calib_put(need, kind_pipe(ly, PIPE_K[a], PIPE_P[b], o), ty, 0);
        }
        calib_need(need, t);
    }
}

static const char *machine(void) {
    static char buf[128];
    size_t len = sizeof buf;
    if (!buf[0] && sysctlbyname("machdep.cpu.brand_string", buf, &len, NULL, 0) != 0)
        strcpy(buf, "unknown");
    return buf;
}

/* the cache: FMM_CALIB_DIR (bench_fmm: results), default ~/Library/Caches/fmm */
static void calib_path(char *buf, size_t len, int f64) {
    const char *dir = getenv("FMM_CALIB_DIR");
    char def[1024];
    if (!dir) {
        const char *home = getenv("HOME");
        snprintf(def, sizeof def, "%s/Library/Caches/fmm", home ? home : ".");
        dir = def;
    }
    snprintf(buf, len, "%s/calib5_%s.txt", dir, f64 ? "f64" : "f32");
}

/* the cache, if it was measured on this machine with this padding, format and D48 program */
static void calib_load(calib_t *c, int f64) {
    char path[256], line[256], kind[16];
    memset(c, 0, sizeof *c);
    const char *re = getenv("FMM_RECALIB");
    if (re && atoi(re)) return;
    calib_path(path, sizeof path, f64);
    FILE *f = fopen(path, "r");
    if (!f) return;
    int ok_machine = 0, ok_pad = 0, ok_format = 0, ok_kernels = 0;
    char kernels[96];
    snprintf(kernels, sizeof kernels, "%s %d R %d", DPS48_PROGRAM, (int)DPS48_OPS, (int)(R336_OPS + R363_OPS + R633_OPS));
    shape_t s;
    double t;
    while (fgets(line, sizeof line, f)) {
        line[strcspn(line, "\n")] = 0;
        if (!strncmp(line, "# machine ", 10)) ok_machine = !strcmp(line + 10, machine());
        else if (!strncmp(line, "# pad ", 6)) ok_pad = (size_t)atol(line + 6) == fmm_pad();
        else if (!strncmp(line, "# format ", 9)) ok_format = atoi(line + 9) == CALIB_FORMAT;
        else if (!strncmp(line, "# kernels ", 10)) ok_kernels = !strcmp(line + 10, kernels);
        else if (line[0] != '#' && sscanf(line, "%15s %zu %zu %zu %lf", kind, &s.m, &s.k, &s.n, &t) == 5 &&
                 kind_parse(kind) >= 0)
            calib_put(c, kind_parse(kind), s, t);
    }
    fclose(f);
    if (!ok_machine || !ok_pad || !ok_format || !ok_kernels) {
        printf("# calibration %s is from another machine, padding, format or D48 program: remeasuring\n", path);
        memset(c, 0, sizeof *c);
    }
}

static void calib_save(const calib_t *c, int f64) {
    char path[256];
    calib_path(path, sizeof path, f64);
    char *slash = strrchr(path, '/');
    if (slash) {                            /* the cache's directory, if it is new */
        *slash = 0;
        if (mkdir(path, 0755) != 0 && errno != EEXIST) perror(path);
        *slash = '/';
    }
    FILE *f = fopen(path, "w");
    if (!f) { perror(path); return; }
    fprintf(f, "# bench_fmm calibration, %s, seconds; entries kind m k n t for a product of shape (m x k)(k x n): "
               "G = one GEMM of that shape, B2 = classical blocked 2x2 (one call each); SW, D48, R336, R363, R633 = "
               "the three passes of one such level whose products have that shape; GSW, GD48, ... = its GEMM time "
               "per product, GkSW, GkD48, ... = the same with k GEMM streams; PYkKpPs, PYkKpPo = pipelined "
               "sub-problems of level Y (steady time, fill and drain); E... = errors at n = N_E\n",
            f64 ? "f64" : "f32");
    fprintf(f, "# machine %s\n# pad %zu\n# format %d\n# kernels %s %d R %d\n", machine(), fmm_pad(), CALIB_FORMAT,
            DPS48_PROGRAM, (int)DPS48_OPS, (int)(R336_OPS + R363_OPS + R633_OPS));
    int idx[CALIB_MAX];
    for (int i = 0; i < c->n; i++) idx[i] = i;
    for (int a = 0; a < c->n; a++)          /* by kind, then shape */
        for (int b = a + 1; b < c->n; b++) {
            int i = idx[a], j = idx[b];
            const shape_t *si = &c->s[i], *sj = &c->s[j];
            int before = c->kind[j] < c->kind[i] ||
                         (c->kind[j] == c->kind[i] &&
                          (sj->m < si->m || (sj->m == si->m && (sj->k < si->k || (sj->k == si->k && sj->n < si->n)))));
            if (before) { idx[a] = j; idx[b] = i; }
        }
    for (int a = 0; a < c->n; a++) {
        int i = idx[a];
        fprintf(f, "%s %zu %zu %zu %.9g\n", kind_name(c->kind[i]), c->s[i].m, c->s[i].k, c->s[i].n, c->t[i]);
    }
    fclose(f);
}

/* predicted seconds for a plan on a problem of shape s below a fused level of type parent (-1:
 * the top), -1 if the calibration lacks an entry it needs (B4, B8 and SW2 are not calibrated, B2
 * only on top) */
static double plan_cost_in(const calib_t *c, const int *plan, shape_t s, int parent) {
    int lv = PLV(plan[0]);
    if (lv == LV_G) {
        if (PNE(plan[0])) return -1;    /* NEON products are not calibrated */
        if (parent < 0) return PST(plan[0]) ? -1 : calib_cost(c, LV_G, s);
        return calib_cost(c, kind_gin(parent, PST(plan[0])), s);
    }
    if (lv == LV_B2) return parent < 0 && shape_sq(s) ? calib_cost(c, LV_B2, s) : -1;
    if (lv_leaf(lv)) return -1;
    if (!lv_divides(lv, s)) return -1;
    shape_t m = lv_sub(lv, s);
    if (PPI(plan[0])) {     /* its passes, then a pipeline of r sub-problems Y over Gk */
        int ly = PLV(plan[1]), lf = plan[2];
        if (lv_leaf(ly) || PLV(lf) != LV_G || PST(lf) == 0 || PNE(lf) || !lv_divides(ly, m)) return -1;
        shape_t my = lv_sub(ly, m);
        int pw = PPW(plan[0]) ? PPW(plan[0]) : fmm_pass_threads();
        double px = calib_cost(c, lv, m), st = calib_cost(c, kind_pipe(ly, PST(lf), pw, 0), my),
               ov = calib_cost(c, kind_pipe(ly, PST(lf), pw, 1), my);
        /* sub-problems under 1 ms are not pipelined: each step costs tens of microseconds of
         * dispatch and their calibration is noisy (2048 f64: 0.3 ms SW sub-problems were
         * predicted 2% faster than the best plan and ran 10% slower) */
        if (st >= 0 && st < 1e-3) return -1;
        return px < 0 || st < 0 || ov < 0 ? -1 : px + lv_rank(lv) * st + ov;
    }
    double p = calib_cost(c, lv, m), below = plan_cost_in(c, plan + 1, m, lv);
    return p < 0 || below < 0 ? -1 : p + lv_rank(lv) * below;
}

static double plan_cost(const calib_t *c, const int *plan, shape_t s) { return plan_cost_in(c, plan, s, -1); }

/* the first entries a plan below parent (-1: the top) can start with: G with every stream count
 * (on top: G alone and B2), then the fused levels; SW2 has the passes of D48 and one product
 * more, and B4, B8 are not calibrated */
static int plan_firsts(int parent, int *out) {
    int k = 0;
    for (int i = 0; i < NSTREAMS; i++)
        if (parent >= 0 || STREAMS[i] == 0) out[k++] = LV_G | (STREAMS[i] << 8);
    if (parent < 0) out[k++] = LV_B2;
    for (int i = 0; i < NFUSED; i++) out[k++] = FUSED[i];
    return k;
}

/* the cheapest plan for a problem of shape s below a level of type parent (-1: the top) under
 * the calibration: dynamic programming over the first entry, a leaf or a fused level over the
 * cheapest plan for its products below it; -1 if nothing is calibrated */
static double plan_best_in(const calib_t *c, shape_t s, int parent, int *plan) {
    double best = -1;
    int firsts[16], nf = plan_firsts(parent, firsts);
    for (int f = 0; f < nf; f++) {
        int e = firsts[f], lv = PLV(e);
        int cand[PLAN_MAX] = {e};
        double t;
        if (lv_leaf(lv)) {
            t = plan_cost_in(c, cand, s, parent);
        } else {
            if (!lv_divides(lv, s) || shape_min(lv_sub(lv, s)) < fmm_minb()) continue;
            shape_t m = lv_sub(lv, s);
            int sub[PLAN_MAX] = {0};
            double below = plan_best_in(c, m, lv, sub), p = calib_cost(c, lv, m);
            memcpy(cand + 1, sub, (PLAN_MAX - 1) * sizeof(int));
            t = below < 0 || p < 0 ? -1 : p + lv_rank(lv) * below;
        }
        if (t >= 0 && (best < 0 || t < best)) {
            best = t;
            memcpy(plan, cand, sizeof cand);
        }
    }
    /* pipelined levels: X+p over Y over Gk */
    for (int fx = 0; fx < NFUSED; fx++)
        for (int fy = 0; fy < NFUSED; fy++)
            for (int a = 0; a < NPIPE_K; a++)
                for (int b = 0; b < NPIPE_P; b++) {
                    int cand[PLAN_MAX] = {FUSED[fx] | (1 << 24) | (PIPE_P[b] << 25), FUSED[fy], LV_G | (PIPE_K[a] << 8)};
                    double t = plan_cost_in(c, cand, s, parent);
                    if (t >= 0 && (best < 0 || t < best)) {
                        best = t;
                        memcpy(plan, cand, sizeof cand);
                    }
                }
    return best;
}

static double plan_best(const calib_t *c, shape_t s, int *plan) { return plan_best_in(c, s, -1, plan); }

/* every plan for n down to blocks of fmm_minb() with its predicted time, cheapest first;
 * returns the count (at most max) */
typedef struct {
    int plan[PLAN_MAX];
    double t;
} ranked_t;

static void plan_enum_rec(const calib_t *c, shape_t n0, shape_t n, int *plan, int depth, ranked_t *out, int *cnt,
                          int max) {
    int firsts[16], nf = plan_firsts(depth ? PLV(plan[depth - 1]) : -1, firsts);
    for (int f = 0; f < nf && *cnt < max && depth < PLAN_MAX - 1; f++) {
        int lv = PLV(firsts[f]);
        plan[depth] = firsts[f];
        if (lv_leaf(lv)) {
            double t = plan_cost(c, plan, n0);
            if (t > 0) {
                memcpy(out[*cnt].plan, plan, sizeof out[*cnt].plan);
                out[(*cnt)++].t = t;
            }
            /* the same with the level two above the leaf pipelined */
            if (depth >= 2 && PST(firsts[f]) > 0 && !lv_leaf(PLV(plan[depth - 1])) && !lv_leaf(PLV(plan[depth - 2])))
                for (int b = 0; b < NPIPE_P && *cnt < max; b++) {
                    int keep = plan[depth - 2];
                    plan[depth - 2] = PLV(keep) | (1 << 24) | (PIPE_P[b] << 25);
                    double tp = plan_cost(c, plan, n0);
                    if (tp > 0) {
                        memcpy(out[*cnt].plan, plan, sizeof out[*cnt].plan);
                        out[(*cnt)++].t = tp;
                    }
                    plan[depth - 2] = keep;
                }
        } else if (lv_divides(lv, n) && shape_min(lv_sub(lv, n)) >= fmm_minb()) {
            plan_enum_rec(c, n0, lv_sub(lv, n), plan, depth + 1, out, cnt, max);
        }
    }
}

static int plan_enum(const calib_t *c, shape_t n, ranked_t *out, int max) {
    int plan[PLAN_MAX] = {0}, cnt = 0;
    plan_enum_rec(c, n, n, plan, 0, out, &cnt, max);
    for (int a = 0; a < cnt; a++)
        for (int b = a + 1; b < cnt; b++)
            if (out[b].t < out[a].t) { ranked_t x = out[a]; out[a] = out[b]; out[b] = x; }
    return cnt;
}

/* ---- the accuracy budget ---------------------------------------------------------------- */
/* a plan's error (max-norm, relative, against the classical GEMM on uniform random inputs) is
 * the classical error scale times one factor per fused level, and grows like sqrt(n) with the
 * size (measured: about 1.4x per doubling, the order of the levels immaterial: SW then D48 and
 * D48 then SW within 2%); the factors come from three plans measured at n = N_E: SW/G, D48/G
 * and D48/D48/G.  Streams and pipelines leave the arithmetic unchanged. */
typedef struct {
    double base, f[LV_N];
    int ok;
} errmod_t;

static errmod_t err_model(const calib_t *c) {
    errmod_t e;
    memset(&e, 0, sizeof e);
    double v[NERR];
    for (int i = 0; i < NERR; i++) {
        v[i] = calib_get(c, K_ERR + i, sq(N_E));
        if (v[i] <= 0) return e;
    }
    e.f[LV_D48] = v[2] / v[1];          /* D48/D48 over D48: the growth of one D48 level */
    e.base = v[1] / e.f[LV_D48];        /* so the classical scale is D48/G's error over that */
    e.f[LV_SW] = v[0] / e.base;
    e.f[LV_SW2] = e.f[LV_SW] * e.f[LV_SW];
    e.f[LV_R336] = v[3] / e.base;
    e.f[LV_R363] = v[4] / e.base;
    e.f[LV_R633] = v[5] / e.base;
    e.ok = 1;
    return e;
}

/* the factor by which a plan's error exceeds the classical GEMM's */
static double plan_growth(const errmod_t *e, const int *plan) {
    double g = 1;
    for (int i = 0; i < PLAN_MAX && !lv_leaf(PLV(plan[i])); i++) g *= e->f[PLV(plan[i])];
    return g;
}

static double plan_err(const errmod_t *e, const int *plan, shape_t s) {
    return e->base * sqrt((double)s.k / N_E) * plan_growth(e, plan);   /* the inner dimension sums k products */
}

static double fmm_max_growth(void) {
    const char *v = getenv("FMM_MAX_GROWTH");
    return v ? atof(v) : 0;
}

/* the cheapest plan whose error growth is at most gmax (0: no limit), -1 if none is calibrated */
static double plan_best_budget(const calib_t *c, shape_t s, double gmax, int *plan) {
    if (gmax <= 0) return plan_best(c, s, plan);
    errmod_t e = err_model(c);
    if (!e.ok) return -1;
    static ranked_t rk[8192];
    int cnt = plan_enum(c, s, rk, 8192);
    for (int i = 0; i < cnt; i++)
        if (plan_growth(&e, rk[i].plan) <= gmax * (1 + 1e-9)) {
            memcpy(plan, rk[i].plan, sizeof rk[i].plan);
            return rk[i].t;
        }
    return -1;
}

/* ---- padding ------------------------------------------------------------------------------ */
/* A plan runs at a shape its levels divide; any other shape is padded: A and B copied into
 * zeroed matrices of the padded shape, the plan run there, the top-left m x n of the result
 * copied to C.  The block sizes need no alignment (Accelerate's GEMM runs within 5% at sizes off
 * multiples of 16, 32, 64), so each dimension rounded up to a multiple of 2^a 3^b (a <= 10, b <=
 * 3) suffices: what plans of 2x2 and 4x4 levels and of the 3x3x6 family divide.  The copies
 * cost about twice the padded matrices' elements of memory traffic (6 N^2 for a square). */
#define PAD_BW 80e9     /* bytes per second of the padding copies */

static double pad_cost(shape_t s, shape_t S, int f64) {
    if (shape_eq(s, S)) return 0;
    double words = (double)S.m * S.k + (double)S.k * S.n + (double)S.m * S.n;
    return 2.0 * words * (f64 ? 8 : 4) / PAD_BW;
}

/* the cheapest plan for s over the padded shapes S >= s (every dimension rounded up to the same
 * multiple), with the padding priced; *spad = S */
static double plan_best_padded(const calib_t *c, shape_t s, double gmax, int f64, int *plan, shape_t *spad) {
    double best = -1;
    shape_t tried[64];
    int nt = 0;
    for (int j = -1; j < 44; j++) {
        size_t d = 1;
        if (j >= 0) {
            for (int a = 0; a < j % 11; a++) d *= 2;
            for (int b = 0; b < j / 11; b++) d *= 3;
        }
        shape_t S = s;
        if (j >= 0) {
            S.m = (s.m + d - 1) / d * d;
            S.k = (s.k + d - 1) / d * d;
            S.n = (s.n + d - 1) / d * d;
        }
        int seen = 0;
        for (int i = 0; i < nt; i++) seen |= shape_eq(tried[i], S);
        if (seen || nt == 64) continue;
        tried[nt++] = S;
        int p[PLAN_MAX];
        double t = plan_best_budget(c, S, gmax, p);
        if (t < 0) continue;
        t += pad_cost(s, S, f64);
        if (best < 0 || t < best) {
            best = t;
            memcpy(plan, p, sizeof p);
            *spad = S;
        }
    }
    return best;
}

/* ---- the entry points (fmm.h) ---------------------------------------------------------- */
static pthread_mutex_t api_lock = PTHREAD_MUTEX_INITIALIZER;
static calib_t *api_cal[2];
static int api_loaded[2];
static void *api_ws;
static size_t api_ws_bytes;
typedef struct {
    shape_t s, spad;
    int f64, plan[PLAN_MAX];
    double gmax, t;
} api_entry;
static api_entry api_plans[64];
static int api_nplans, api_next;

static calib_t *api_calib(int f64) {
    if (!api_loaded[f64]) {
        api_cal[f64] = calloc(1, sizeof(calib_t));
        if (api_cal[f64]) calib_load(api_cal[f64], f64);
        api_loaded[f64] = 1;
    }
    return api_cal[f64];
}

/* the plan for (shape, precision, budget) and the shape S >= s it runs at (padded if S > s):
 * from the plans already made, else the planner (the classical GEMM where the calibration does
 * not cover the shape); t: its predicted time, -1 if none */
static void api_plan(shape_t s, int f64, double gmax, int *plan, shape_t *spad, double *t) {
    for (int i = 0; i < api_nplans; i++)
        if (shape_eq(api_plans[i].s, s) && api_plans[i].f64 == f64 && api_plans[i].gmax == gmax) {
            memcpy(plan, api_plans[i].plan, sizeof api_plans[i].plan);
            *spad = api_plans[i].spad;
            if (t) *t = api_plans[i].t;
            return;
        }
    calib_t *c = api_calib(f64);
    int p[PLAN_MAX] = {LV_G};
    shape_t S = s;
    double tt = c ? plan_best_padded(c, s, gmax, f64, p, &S) : -1;
    if (tt < 0) {
        memset(p, 0, sizeof p);
        p[0] = LV_G;
        S = s;
    }
    api_entry *e = &api_plans[api_next];
    api_next = (api_next + 1) % 64;
    if (api_nplans < 64) api_nplans++;
    e->s = s;
    e->spad = S;
    e->f64 = f64;
    e->gmax = gmax;
    e->t = tt;
    memcpy(e->plan, p, sizeof p);
    memcpy(plan, p, sizeof p);
    *spad = S;
    if (t) *t = tt;
}

#define T float
#define SUF f
#define GEMM cblas_sgemm
#define NEON_GEMM_ROWS neon_sgemm_rows
#define FMM_FLOAT 1
#include "fmm_impl.h"
#undef FMM_FLOAT
#undef T
#undef SUF
#undef GEMM
#undef NEON_GEMM_ROWS
#define T double
#define SUF d
#define GEMM cblas_dgemm
#define NEON_GEMM_ROWS neon_dgemm_rows
#include "fmm_impl.h"
#undef T
#undef SUF
#undef GEMM
#undef NEON_GEMM_ROWS

int fmm_sgemm(size_t n, const float *A, size_t lda, const float *B, size_t ldb, float *C, size_t ldc,
              double max_growth) {
    return api_gemmf(sq(n), A, lda, B, ldb, C, ldc, max_growth);
}

int fmm_dgemm(size_t n, const double *A, size_t lda, const double *B, size_t ldb, double *C, size_t ldc,
              double max_growth) {
    return api_gemmd(sq(n), A, lda, B, ldb, C, ldc, max_growth);
}

int fmm_sgemm_mkn(size_t m, size_t k, size_t n, const float *A, size_t lda, const float *B, size_t ldb, float *C,
                  size_t ldc, double max_growth) {
    shape_t s = {m, k, n};
    return api_gemmf(s, A, lda, B, ldb, C, ldc, max_growth);
}

int fmm_dgemm_mkn(size_t m, size_t k, size_t n, const double *A, size_t lda, const double *B, size_t ldb, double *C,
                  size_t ldc, double max_growth) {
    shape_t s = {m, k, n};
    return api_gemmd(s, A, lda, B, ldb, C, ldc, max_growth);
}

int fmm_calibrate(size_t n, int f64) { return f64 ? api_calibrated(sq(n)) : api_calibratef(sq(n)); }

int fmm_calibrate_mkn(size_t m, size_t k, size_t n, int f64) {
    shape_t s = {m, k, n};
    return f64 ? api_calibrated(s) : api_calibratef(s);
}

static const char *plan_of_shape(shape_t s, int f64, double max_growth, double *predicted) {
    static char buf[160];
    int plan[PLAN_MAX];
    shape_t S;
    double t;
    pthread_mutex_lock(&api_lock);
    api_plan(s, f64 != 0, max_growth, plan, &S, &t);
    plan_str(plan, buf, sizeof buf);
    if (!shape_eq(S, s)) {
        if (shape_sq(S)) snprintf(buf + strlen(buf), sizeof buf - strlen(buf), " padded to %zu", S.m);
        else snprintf(buf + strlen(buf), sizeof buf - strlen(buf), " padded to %zux%zux%zu", S.m, S.k, S.n);
    }
    pthread_mutex_unlock(&api_lock);
    if (predicted) *predicted = t;
    return buf;
}

const char *fmm_plan(size_t n, int f64, double max_growth, double *predicted) {
    return plan_of_shape(sq(n), f64, max_growth, predicted);
}

const char *fmm_plan_mkn(size_t m, size_t k, size_t n, int f64, double max_growth, double *predicted) {
    shape_t s = {m, k, n};
    return plan_of_shape(s, f64, max_growth, predicted);
}

void fmm_release(void) {
    pthread_mutex_lock(&api_lock);
    free(api_ws);
    api_ws = NULL;
    api_ws_bytes = 0;
    for (int f = 0; f < 2; f++) {
        free(api_cal[f]);
        api_cal[f] = NULL;
        api_loaded[f] = 0;
    }
    api_nplans = api_next = 0;
    pthread_mutex_unlock(&api_lock);
}
