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
 *   auto       the plan the calibrated cost model picks for n; auto:g the fastest plan whose
 *              error grows at most g-fold over the classical GEMM's (FMM_MAX_GROWTH=g for auto)
 *   M@k        method M with the GEMMs of its lowest level as k single-threaded streams taking
 *              products in turn (leaf Gk in a plan; G alone = Accelerate's own threading, one
 *              product at a time)
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
#include <ctype.h>
#include <math.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/sysctl.h>
#include <time.h>

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
enum { LV_NONE = -1, LV_G = 0, LV_B2, LV_B4, LV_B8, LV_SW, LV_D48, LV_SW2, LV_N };
static const char *LV_NAME[LV_N] = {"G", "B2", "B4", "B8", "SW", "D48", "SW2"};
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
static int lv_grid(int lv) {
    static const int g[LV_N] = {1, 2, 4, 8, 2, 4, 4};
    return lv < 0 ? 1 : g[lv];
}
static int lv_rank(int lv) { return lv == LV_SW ? 7 : lv == LV_D48 ? 48 : 49; }

/* scratch elements a plan needs at size n: each fused level 3 r blocks of m*m + pad (S, T, M);
 * the levels below reuse their scratch product after product */
static size_t plan_work(const int *plan, size_t n) {
    int lv = PLV(plan[0]);
    if (lv_leaf(lv)) return 0;
    size_t m = n / lv_grid(lv);
    /* a pipelined level double-buffers the scratch of the level below */
    return (size_t)3 * lv_rank(lv) * (m * m + fmm_pad()) + (PPI(plan[0]) ? 2 : 1) * plan_work(plan + 1, m);
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
 * streams; 0 if the method is not a plan or the plan does not divide n */
static int parse_plan(const char *meth, size_t n, int *plan) {
    static const struct { const char *name, *levels; } NAMED[] = {
        {"classical", "G"},        {"blk2", "B2"},         {"blk4", "B4"},
        {"blk8", "B8"},            {"sw1", "SW/G"},        {"sw2rec", "SW/SW/G"},
        {"sw3rec", "SW/SW/SW/G"},  {"sw4rec", "SW/SW/SW/SW/G"},
        {"sw2", "SW2/G"},          {"sw2sw", "SW2/SW/G"},  {"dps48", "D48/G"},
        {"dps48sw", "D48/SW/G"},   {"dps48x2", "D48/D48/G"},
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
    size_t sz = n;
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
        if (found < 0 || sz % lv_grid(found)) return 0;
        sz /= lv_grid(found);
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
#define K_PIPE 1000 /* K_PIPE + ((16 k + p) 2 + part) 8 + level: pipelined sub-problems */
#define K_ERR 9000  /* K_ERR + 0, 1, 2: errors of SW/G, D48/G, D48/D48/G at n = N_E */
#define N_E 2048
#define CALIB_FORMAT 4
static const int PIPE_K[] = {3, 6}, PIPE_P[] = {2, 3, 4};  /* the pipelines the planner considers */
#define NPIPE_K ((int)(sizeof PIPE_K / sizeof PIPE_K[0]))
#define NPIPE_P ((int)(sizeof PIPE_P / sizeof PIPE_P[0]))
#define CALIB_MAX 1024
typedef struct {
    int kind[CALIB_MAX], n;
    size_t m[CALIB_MAX];
    double t[CALIB_MAX];
} calib_t;

static int kind_gin(int lv, int streams) { return K_GIN + 16 * streams + lv; }
static int kind_pipe(int lv, int streams, int passes, int over) {
    return K_PIPE + ((16 * streams + passes) * 2 + over) * 8 + lv;
}

static const char *kind_name(int kind) {
    static char buf[4][24];
    static int k;
    if (kind < K_GIN) return LV_NAME[kind];
    k = (k + 1) % 4;
    if (kind >= K_ERR) {
        static const char *E[3] = {"ESW", "ED48", "ED48D48"};
        return E[kind - K_ERR];
    }
    if (kind >= K_PIPE) {
        int x = kind - K_PIPE, lv = x % 8, over = (x / 8) % 2, sp = x / 16;
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
    if (!strcmp(s, "ESW")) return K_ERR;
    if (!strcmp(s, "ED48")) return K_ERR + 1;
    if (!strcmp(s, "ED48D48")) return K_ERR + 2;
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
 * fused level its passes and per-product GEMM (every stream count) at blocks n/g, and the
 * needs of n/g */
static void calib_need(calib_t *need, size_t n) {
    if (n >= N_E)                           /* the error model, measured at N_E */
        for (int i = 0; i < 3; i++) calib_put(need, K_ERR + i, N_E, 0);
    calib_put(need, LV_G, n, 0);
    if (n % 2 == 0 && n / 2 >= fmm_minb()) calib_put(need, LV_B2, n, 0);
    for (int lv = LV_SW; lv <= LV_D48; lv++) {
        size_t g = lv_grid(lv);
        if (n % g || n / g < fmm_minb()) continue;
        calib_put(need, lv, n / g, 0);
        for (int i = 0; i < NSTREAMS; i++) calib_put(need, kind_gin(lv, STREAMS[i]), n / g, 0);
        /* a pipelined level at n: its sub-problems are levels ly with blocks n / g / gy */
        for (int ly = LV_SW; ly <= LV_D48; ly++) {
            size_t gy = lv_grid(ly), my = n / g / gy;
            if ((n / g) % gy || my < fmm_minb()) continue;
            for (int a = 0; a < NPIPE_K; a++)
                for (int b = 0; b < NPIPE_P; b++)
                    for (int o = 0; o < 2; o++) calib_put(need, kind_pipe(ly, PIPE_K[a], PIPE_P[b], o), my, 0);
        }
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
               "with blocks of size m; GSW m, GD48 m = its GEMM time per product, GkSW m, GkD48 m = the "
               "same with k GEMM streams\n",
            f64 ? "f64" : "f32");
    fprintf(f, "# machine %s\n# pad %zu\n# format %d\n", machine(), fmm_pad(), CALIB_FORMAT);
    for (int v = 0; v < K_ERR + 3; v++)   /* by kind, then size */
        for (size_t m = 1; m < ((size_t)1 << 40); m *= 2)
            for (int i = 0; i < c->n; i++)
                if (c->kind[i] == v && c->m[i] >= m && c->m[i] < 2 * m)
                    fprintf(f, "%s %zu %.9g\n", kind_name(v), c->m[i], c->t[i]);
    fclose(f);
}

/* predicted seconds for a plan at size n below a fused level of type parent (-1: the top), -1
 * if the calibration lacks an entry it needs (B4, B8 and SW2 are not calibrated, B2 only on top) */
static double plan_cost_in(const calib_t *c, const int *plan, size_t n, int parent) {
    int lv = PLV(plan[0]);
    if (lv == LV_G) {
        if (PNE(plan[0])) return -1;    /* NEON products are not calibrated */
        if (parent < 0) return PST(plan[0]) ? -1 : calib_get(c, LV_G, n);
        return calib_get(c, kind_gin(parent, PST(plan[0])), n);
    }
    if (lv == LV_B2) return parent < 0 ? calib_get(c, LV_B2, n) : -1;
    if (lv_leaf(lv)) return -1;
    size_t g = lv_grid(lv), m = n / g;
    if (n % g) return -1;
    if (PPI(plan[0])) {     /* its passes, then a pipeline of r sub-problems Y over Gk */
        int ly = PLV(plan[1]), lf = plan[2];
        if (lv_leaf(ly) || PLV(lf) != LV_G || PST(lf) == 0 || PNE(lf) || m % lv_grid(ly)) return -1;
        size_t my = m / lv_grid(ly);
        int pw = PPW(plan[0]) ? PPW(plan[0]) : fmm_pass_threads();
        double px = calib_get(c, lv, m), st = calib_get(c, kind_pipe(ly, PST(lf), pw, 0), my),
               ov = calib_get(c, kind_pipe(ly, PST(lf), pw, 1), my);
        /* sub-problems under 1 ms are not pipelined: each step costs tens of microseconds of
         * dispatch and their calibration is noisy (2048 f64: 0.3 ms SW sub-problems were
         * predicted 2% faster than the best plan and ran 10% slower) */
        if (st >= 0 && st < 1e-3) return -1;
        return px < 0 || st < 0 || ov < 0 ? -1 : px + lv_rank(lv) * st + ov;
    }
    double p = calib_get(c, lv, m), below = plan_cost_in(c, plan + 1, m, lv);
    return p < 0 || below < 0 ? -1 : p + lv_rank(lv) * below;
}

static double plan_cost(const calib_t *c, const int *plan, size_t n) { return plan_cost_in(c, plan, n, -1); }

/* the first entries a plan below parent (-1: the top) can start with: G with every stream count
 * (on top: G alone and B2), SW, D48; SW2 has the passes of D48 and one product more, and B4, B8
 * are not calibrated */
static int plan_firsts(int parent, int *out) {
    int k = 0;
    for (int i = 0; i < NSTREAMS; i++)
        if (parent >= 0 || STREAMS[i] == 0) out[k++] = LV_G | (STREAMS[i] << 8);
    if (parent < 0) out[k++] = LV_B2;
    out[k++] = LV_SW;
    out[k++] = LV_D48;
    return k;
}

/* the cheapest plan for n below a level of type parent (-1: the top) under the calibration:
 * dynamic programming over the first entry, a leaf or a fused level over the cheapest plan for
 * n/g below it; -1 if nothing is calibrated */
static double plan_best_in(const calib_t *c, size_t n, int parent, int *plan) {
    double best = -1;
    int firsts[16], nf = plan_firsts(parent, firsts);
    for (int f = 0; f < nf; f++) {
        int e = firsts[f], lv = PLV(e);
        int cand[PLAN_MAX] = {e};
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
    /* pipelined levels: X+p over Y over Gk */
    for (int lx = LV_SW; lx <= LV_D48; lx++)
        for (int ly = LV_SW; ly <= LV_D48; ly++)
            for (int a = 0; a < NPIPE_K; a++)
                for (int b = 0; b < NPIPE_P; b++) {
                    int cand[PLAN_MAX] = {lx | (1 << 24) | (PIPE_P[b] << 25), ly, LV_G | (PIPE_K[a] << 8)};
                    double t = plan_cost_in(c, cand, n, parent);
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
    double pred, perr;
} meth_t;

/* every plan for n down to blocks of fmm_minb() with its predicted time, cheapest first;
 * returns the count (at most max) */
typedef struct {
    int plan[PLAN_MAX];
    double t;
} ranked_t;

static void plan_enum_rec(const calib_t *c, size_t n0, size_t n, int *plan, int depth, ranked_t *out, int *cnt,
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
    double esw = calib_get(c, K_ERR, N_E), e1 = calib_get(c, K_ERR + 1, N_E), e2 = calib_get(c, K_ERR + 2, N_E);
    if (esw <= 0 || e1 <= 0 || e2 <= 0) return e;
    e.f[LV_D48] = e2 / e1;
    e.base = e1 / e.f[LV_D48];
    e.f[LV_SW] = esw / e.base;
    e.f[LV_SW2] = e.f[LV_SW] * e.f[LV_SW];
    e.ok = 1;
    return e;
}

/* the factor by which a plan's error exceeds the classical GEMM's */
static double plan_growth(const errmod_t *e, const int *plan) {
    double g = 1;
    for (int i = 0; i < PLAN_MAX && !lv_leaf(PLV(plan[i])); i++) g *= e->f[PLV(plan[i])];
    return g;
}

static double plan_err(const errmod_t *e, const int *plan, size_t n) {
    return e->base * sqrt((double)n / N_E) * plan_growth(e, plan);
}

static double fmm_max_growth(void) {
    const char *v = getenv("FMM_MAX_GROWTH");
    return v ? atof(v) : 0;
}

/* the cheapest plan whose error growth is at most gmax (0: no limit), -1 if none is calibrated */
static double plan_best_budget(const calib_t *c, size_t n, double gmax, int *plan) {
    if (gmax <= 0) return plan_best(c, n, plan);
    errmod_t e = err_model(c);
    if (!e.ok) return -1;
    static ranked_t rk[8192];
    int cnt = plan_enum(c, n, rk, 8192);
    for (int i = 0; i < cnt; i++)
        if (plan_growth(&e, rk[i].plan) <= gmax * (1 + 1e-9)) {
            memcpy(plan, rk[i].plan, sizeof rk[i].plan);
            return rk[i].t;
        }
    return -1;
}

#define T float
#define SUF f
#define GEMM cblas_sgemm
#define NEON_GEMM_ROWS neon_sgemm_rows
#include "bench_impl.h"
#undef T
#undef SUF
#undef GEMM
#undef NEON_GEMM_ROWS
#define T double
#define SUF d
#define GEMM cblas_dgemm
#define NEON_GEMM_ROWS neon_dgemm_rows
#include "bench_impl.h"
#undef T
#undef SUF
#undef GEMM
#undef NEON_GEMM_ROWS

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
