/* bench_impl.h: one precision of the benchmark driver (bench_fmm.c), on top of the library's
 * fmm_impl.h: the 48-scheme op by op, the GEMM timing probe, the plan table and the timed
 * comparison of methods. */

#define CAT_(a, b) a##b
#define CAT(a, b) CAT_(a, b)
#define FN(name) CAT(name, SUF)

#include "gemms_impl.h"   /* the ESSL _GEMMS baseline (method gemms:L) */

/* one elementwise block operation over m rows of m: dst = a (+ - ) b, or a * c, a / c */
static void FN(blockop)(int kind, size_t m, T *dst, size_t ldd, const T *a, size_t lda, const T *b,
                        size_t ldb, int cst) {
    size_t chunks = 64, step = (m + chunks - 1) / chunks;
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
        size_t r0 = ch * step, r1 = r0 + step < m ? r0 + step : m;
        for (size_t r = r0; r < r1; r++) {
            T *restrict d = dst + r * ldd;
            const T *restrict x = a + r * lda;
            const T *restrict y = b ? b + r * ldb : NULL;
            switch (kind) {
            case 0: memcpy(d, x, m * sizeof(T)); break;
            case 1: for (size_t c = 0; c < m; c++) d[c] = x[c] + y[c]; break;
            case 2: for (size_t c = 0; c < m; c++) d[c] = x[c] - y[c]; break;
            case 3: for (size_t c = 0; c < m; c++) d[c] = x[c] * (T)cst; break;
            default: for (size_t c = 0; c < m; c++) d[c] = x[c] / (T)cst; break;
            }
        }
    });
}

/* a program run one block operation at a time (one pass over memory per operation); refs:
 * input k, temp 100000 + t, output 200000 + o; temps get their own m*m buffers */
static void FN(run_ops)(const int (*ops)[4], int len, size_t m, const T *const *in, size_t ld_in, T *const *out,
                        size_t ld_out, T **temps) {
    for (int q = 0; q < len; q++) {
        int dst = ops[q][0], kind = ops[q][1], a = ops[q][2], b = ops[q][3];
#define REF(v, ptr, ld)                                                                            \
    do {                                                                                           \
        if ((v) >= 200000) { ptr = out[(v) - 200000]; ld = ld_out; }                               \
        else if ((v) >= 100000) { ptr = temps[(v) - 100000]; ld = m; }                             \
        else { ptr = (T *)in[(v)]; ld = ld_in; }                                                   \
    } while (0)
        T *pd, *pa, *pb = NULL;
        size_t ldd, lda, ldb = 0;
        REF(dst, pd, ldd);
        REF(a, pa, lda);
        if (kind == 1 || kind == 2) REF(b, pb, ldb);
#undef REF
        FN(blockop)(kind, m, pd, ldd, pa, lda, pb, ldb, (kind >= 3) ? b : 0);
    }
}

static void FN(dps48_opbyop)(size_t n, const T *A, const T *B, T *C, T *work, T **temps, FN(split_t) *sp) {
    int g = 4, r = 48;
    size_t m = n / g;
    const T *Ab[16], *Bb[16];
    T *Cb[16], *S[48], *Tt[48], *M[48];
    for (int k = 0; k < 16; k++) {
        Ab[k] = A + (k / g) * m * n + (k % g) * m;
        Bb[k] = B + (k / g) * m * n + (k % g) * m;
        Cb[k] = C + (k / g) * m * n + (k % g) * m;
    }
    for (int k = 0; k < r; k++) {
        S[k] = work + (size_t)k * m * m;
        Tt[k] = work + (size_t)(r + k) * m * m;
        M[k] = work + (size_t)(2 * r + k) * m * m;
    }
    double t0 = now();
    FN(run_ops)(dps48_L_ops, dps48_L_ops_len, m, Ab, n, S, m, temps);
    double t1 = now();
    FN(run_ops)(dps48_R_ops, dps48_R_ops_len, m, Bb, n, Tt, m, temps);
    double t2 = now();
    for (int k = 0; k < r; k++) FN(gemm)(sq(m), S[k], m, Tt[k], m, M[k], m);
    double t3 = now();
    FN(run_ops)(dps48_P_ops, dps48_P_ops_len, m, (const T *const *)M, m, Cb, n, temps);
    double t4 = now();
    if (sp) {
        sp->tL += t1 - t0;
        sp->tR += t2 - t1;
        sp->tG += t3 - t2;
        sp->tP += t4 - t3;
    }
}

/* GEMM time per product at size m, three ways: one GEMM on the same buffers after an eviction
 * (the calibration), a stream of K GEMMs on distinct operands spaced like scratch blocks, and
 * inside a fused D48 level (its GEMM time / 48); medians of reps */
static void FN(gemm_probe)(size_t n) {
    size_t nn = n * n;
    int f64 = sizeof(T) == 8;
    T *A = alloc_t(nn * sizeof(T)), *B = alloc_t(nn * sizeof(T)), *C = alloc_t(nn * sizeof(T));
    for (size_t i = 0; i < nn; i++) { A[i] = (T)1 / (T)(1 + i % 7); B[i] = (T)1 / (T)(1 + i % 5); C[i] = 0; }
    int top[2] = {LV_D48, LV_G};
    size_t wsz = plan_work(top, sq(n));
    T *work = alloc_t(wsz * sizeof(T));
    memset(work, 0, wsz * sizeof(T));
    for (size_t m = 256; 4 * m <= n; m *= 2) {
        int pg[2] = {LV_G, LV_NONE};
        double single = FN(time_plan)(pg, sq(m), A, B, C, work);
        size_t bs = m * m + fmm_pad();
        int K = (int)(wsz / (3 * bs));
        if (K > 48) K = 48;
        double ts[9], tl[9];
        for (int q = 0; q < 9; q++) {
            evict();
            double t = now();
            for (int k = 0; k < K; k++)
                FN(gemm)(sq(m), work + (size_t)k * bs, m, work + (size_t)(K + k) * bs, m, work + (size_t)(2 * K + k) * bs, m);
            ts[q] = (now() - t) / K;
            FN(split_t) sp = {0};
            evict();
            FN(exec)(top, sq(4 * m), A, 4 * m, B, 4 * m, C, 4 * m, work, &sp);
            tl[q] = sp.tG / 48;
        }
        for (int a = 0; a < 9; a++)
            for (int b = a + 1; b < 9; b++) {
                if (ts[b] < ts[a]) { double x = ts[a]; ts[a] = ts[b]; ts[b] = x; }
                if (tl[b] < tl[a]) { double x = tl[a]; tl[a] = tl[b]; tl[b] = x; }
            }
        printf("%s m=%-5zu single %.6f  stream(K=%d) %.6f (%+.1f%%)  in D48 level %.6f (%+.1f%%)\n",
               f64 ? "f64" : "f32", m, single, K, ts[4], 100 * (ts[4] / single - 1), tl[4],
               100 * (tl[4] / single - 1));
        fflush(stdout);
    }
    free(work);
    free(A); free(B); free(C);
}

/* calibrate for n, then for each size n, n/2, ... down to 1024: the planner's choice and the
 * predicted times of the named plans */
static void FN(plan_table)(size_t n) {
    size_t nn = n * n;
    int f64 = sizeof(T) == 8;
    T *A = alloc_t(nn * sizeof(T)), *B = alloc_t(nn * sizeof(T)), *C = alloc_t(nn * sizeof(T));
    for (size_t i = 0; i < nn; i++) { A[i] = (T)1 / (T)(1 + i % 7); B[i] = (T)1 / (T)(1 + i % 5); C[i] = 0; }
    calib_t *cal = calloc(1, sizeof(calib_t));
    calib_load(cal, f64);
    FN(calibrate)(cal, sq(n), A, B, C);
    static const char *NAMED[] = {"classical", "blk2", "sw1", "sw2rec", "sw3rec", "sw4rec", "dps48",
                                  "dps48sw", "dps48x2", "r336", "r336x2", "r336x3", "swr336"};
    for (size_t sz = n; sz >= 1024 && sz % 2 == 0; sz /= 2) {
        int plan[PLAN_MAX];
        char ps[128];
        double best = plan_best(cal, sq(sz), plan);
        if (best < 0) break;
        plan_str(plan, ps, sizeof ps);
        printf("n=%-6zu %s  best %-16s %8.4f s ", sz, f64 ? "f64" : "f32", ps, best);
        for (size_t i = 0; i < sizeof NAMED / sizeof NAMED[0]; i++) {
            int p2[PLAN_MAX];
            double t = parse_plan(NAMED[i], sq(sz), p2) ? plan_cost(cal, p2, sq(sz)) : -1;
            if (t > 0) printf(" %s %.4f", NAMED[i], t);
        }
        printf("\n");
        static ranked_t rk[4096];
        int cnt = plan_enum(cal, sq(sz), rk, 4096);
        printf("         top:");
        for (int i = 0; i < cnt && i < 6; i++) {
            plan_str(rk[i].plan, ps, sizeof ps);
            printf(" %s %.4f%s", ps, rk[i].t, i + 1 < cnt && i < 5 ? "," : "");
        }
        printf("  (%d plans)\n", cnt);
        errmod_t e = err_model(cal);
        if (e.ok) {
            printf("         error growth over classical: best %.2f (pred. error %.1e);", plan_growth(&e, plan, sq(sz)),
                   plan_err(&e, plan, sq(sz)));
            static const double BUDGET[] = {16, 8, 4, 2};
            for (int b = 0; b < 4; b++) {
                int pb[PLAN_MAX];
                double t = plan_best_budget(cal, sq(sz), BUDGET[b], pb);
                if (t < 0) continue;
                plan_str(pb, ps, sizeof ps);
                printf(" <=%g: %s %.4f s%s", BUDGET[b], ps, t, b < 3 ? "," : "");
            }
            printf("\n");
        }
    }
    if (n >= N_E) {
        print_errmodel(cal, sizeof(T) == 4 ? 0x1p-24 : 0x1p-53);
    }
    free(cal);
    free(A); free(B); free(C);
}

/* FMM_PRESCALE=2, 3: the library's prescaling inside the timed run, as separate passes over copies
 * (2) or folded into the top level's passes (3); unpadded plans only */
static int FN(ps_mode);
static T *FN(ps_copies);

static void FN(run_method)(const meth_t *q, shape_t s, const T *A, const T *B, T *C, T *work, T **temps,
                           FN(split_t) *sp) {
    if (q->is_plan && FN(ps_mode) >= 2 && shape_eq(q->spad, s) && !lv_leaf(PLV(q->plan[0])))
        FN(exec_prescaled)(FN(ps_mode) - 1, q->plan, s, A, s.k, B, s.n, C, s.n, work, FN(ps_copies), sp);
    else if (q->is_plan) FN(exec_padded)(q->plan, s, q->spad, A, s.k, B, s.n, C, s.n, work, sp);
    else if (q->gemms) FN(gemms)(q->gemms, s.m, s.k, s.n, A, s.k, B, s.n, C, s.n, work);
    else FN(dps48_opbyop)(s.m, A, B, C, work, temps, sp);
}

/* the timed comparison on a problem of shape s = (M x K)(K x N) (square: -n N; -M -K -N otherwise) */
static void FN(bench)(shape_t s0, const char *methods, int reps) {
    size_t n = s0.m, na = s0.m * s0.k, nb = s0.k * s0.n, nn = s0.m * s0.n;
    int f64 = sizeof(T) == 8, square = shape_sq(s0);
    char shp[48];
    if (square) snprintf(shp, sizeof shp, "n=%-6zu", n);
    else snprintf(shp, sizeof shp, "%zux%zux%zu", s0.m, s0.k, s0.n);
    T *A = alloc_t(na * sizeof(T)), *B = alloc_t(nb * sizeof(T)), *C = alloc_t(nn * sizeof(T)),
      *Cref = alloc_t(nn * sizeof(T));
    uint64_t s = 0x9e3779b97f4a7c15ull;
    const char *seed = getenv("FMM_SEED");         /* another random instance */
    if (seed) s ^= (uint64_t)strtoull(seed, NULL, 0) * 0xbf58476d1ce4e5b9ull;
    size_t nmax = na > nb ? na : nb;
    for (size_t i = 0; i < nmax; i++) {          /* the same stream as the square case for A and B of equal size */
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        if (i < na) A[i] = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        if (i < nb) B[i] = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
    }
    /* FMM_NORMAL=1: standard normal inputs instead (Box-Muller on the same stream), as in the
     * experiments of Dumas, Pernet and Sedoglavic (arXiv:2603.18699, Figure 1) */
    const char *nrm = getenv("FMM_NORMAL");
    if (nrm && atoi(nrm))
        for (size_t i = 0; i < nmax; i++)
            for (int w = 0; w < 2; w++) {
                s ^= s << 13; s ^= s >> 7; s ^= s << 17;
                double u1 = ((double)(s >> 11) + 1) / 9007199254740993.0;
                s ^= s << 13; s ^= s >> 7; s ^= s << 17;
                double u2 = (double)(s >> 11) / 9007199254740992.0;
                double z = sqrt(-2 * log(u1)) * cos(2 * M_PI * u2);
                if (w == 0 && i < na) A[i] = (T)z;
                if (w == 1 && i < nb) B[i] = (T)z;
            }
    /* FMM_INPUT: badly scaled inputs for the error study (on top of the distribution above)
     *   nonneg     |A| and |B|
     *   outer:s    row i of A times 10^(-s i/(M-1)), column j of B times 10^(-s j/(N-1)): C's entries
     *              range over 2s decades, the max-norm error sees only the largest
     *   inner:s    column l of A times 10^(s (l/(K-1) - 1/2)), row l of B divided by the same: C is
     *              unchanged, the inputs' norms grow by 10^(s/2) each
     *   outerp:s, innerp:s  the same factors in a scrambled order (i -> 7919 i mod M)
     *   cross:s    the off-diagonal halves of A and of B times 10^-s: no diagonal scaling evens it
     *   entry:s    every entry times its own 10^(-s U), U uniform in [0,1): neither */
    const char *inp = getenv("FMM_INPUT");
    if (inp && *inp) {
        double sc = 0;
        const char *colon = strchr(inp, ':');
        if (colon) sc = atof(colon + 1);
        int perm = !strncmp(inp, "outerp", 6) || !strncmp(inp, "innerp", 6);
#define PI_(i, len) (perm ? (size_t)(((unsigned long long)(i) * 7919ull) % (len)) : (size_t)(i))
        if (!strcmp(inp, "nonneg")) {
            for (size_t i = 0; i < na; i++) A[i] = (T)fabs((double)A[i]);
            for (size_t i = 0; i < nb; i++) B[i] = (T)fabs((double)B[i]);
        } else if (!strncmp(inp, "outer", 5)) {
            for (size_t i = 0; i < s0.m; i++) {
                double f = pow(10, -sc * (double)PI_(i, s0.m) / (double)(s0.m - 1));
                for (size_t l = 0; l < s0.k; l++) A[i * s0.k + l] = (T)(A[i * s0.k + l] * f);
            }
            for (size_t j = 0; j < s0.n; j++) {
                double f = pow(10, -sc * (double)PI_(j, s0.n) / (double)(s0.n - 1));
                for (size_t l = 0; l < s0.k; l++) B[l * s0.n + j] = (T)(B[l * s0.n + j] * f);
            }
        } else if (!strncmp(inp, "inner", 5)) {
            for (size_t l = 0; l < s0.k; l++) {
                double f = pow(10, sc * ((double)PI_(l, s0.k) / (double)(s0.k - 1) - 0.5));
                for (size_t i = 0; i < s0.m; i++) A[i * s0.k + l] = (T)(A[i * s0.k + l] * f);
                for (size_t j = 0; j < s0.n; j++) B[l * s0.n + j] = (T)(B[l * s0.n + j] / f);
            }
        } else if (!strncmp(inp, "cross:", 6)) {
            for (size_t i = 0; i < s0.m; i++)
                for (size_t l = 0; l < s0.k; l++)
                    if ((i < s0.m / 2) != (l < s0.k / 2)) A[i * s0.k + l] = (T)(A[i * s0.k + l] * pow(10, -sc));
            for (size_t l = 0; l < s0.k; l++)
                for (size_t j = 0; j < s0.n; j++)
                    if ((l < s0.k / 2) != (j < s0.n / 2)) B[l * s0.n + j] = (T)(B[l * s0.n + j] * pow(10, -sc));
        } else if (!strncmp(inp, "entry:", 6)) {
            for (size_t i = 0; i < nmax; i++)
                for (int w = 0; w < 2; w++) {
                    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
                    double f = pow(10, -sc * (double)(s >> 11) / 9007199254740992.0);
                    if (w == 0 && i < na) A[i] = (T)(A[i] * f);
                    if (w == 1 && i < nb) B[i] = (T)(B[i] * f);
                }
        } else {
            fprintf(stderr, "unknown FMM_INPUT %s\n", inp);
            exit(1);
        }
#undef PI_
        printf("# inputs %s\n", inp);
    }
    /* the methods: plans (named, plan=..., auto) or the op-by-op program; the calibration is
     * measured for auto and otherwise read from the cache, if there is one, for predictions */
    calib_t *cal = calloc(1, sizeof(calib_t));
    calib_load(cal, f64);
    char buf[512];
    meth_t ms[16];
    int nm = 0;
    strncpy(buf, methods, sizeof buf - 1);
    buf[sizeof buf - 1] = 0;
    char *save = NULL;
    for (char *tok = strtok_r(buf, ",", &save); tok && nm < 16; tok = strtok_r(NULL, ",", &save)) {
        meth_t *q = &ms[nm];
        memset(q, 0, sizeof *q);
        q->name = tok;
        q->spad = s0;
        if (!strncmp(tok, "auto", 4) && (tok[4] == 0 || tok[4] == ':')) {
            /* auto: the default budget (FMM_MAX_GROWTH if set); auto:g that budget; auto:none the fastest plan */
            double gmax = tok[4] != ':' ? fmm_max_growth()
                          : (!strcmp(tok + 5, "none") || !strcmp(tok + 5, "fast")) ? -1 : atof(tok + 5);
            FN(calibrate)(cal, s0, A, B, C);  /* exactly for this shape: rectangular sub-shapes do not interpolate */
            q->pred = plan_best_padded(cal, s0, gmax, f64, q->plan, &q->spad);
            if (q->pred < 0) {
                printf("%s: nothing calibrated for %s\n", tok, shp);
                continue;
            }
            q->is_plan = 1;
            char ps[128];
            plan_str(q->plan, ps, sizeof ps);
            printf("# %s %s %s: plan %s", tok, shp, f64 ? "f64" : "f32", ps);
            if (!shape_eq(q->spad, s0)) printf(" padded to %zux%zux%zu", q->spad.m, q->spad.k, q->spad.n);
            printf(", predicted %.3f s\n", q->pred);
        } else if (!strncmp(tok, "gemms:", 6) && atoi(tok + 6) >= 1 && atoi(tok + 6) <= 6) {
            q->gemms = atoi(tok + 6);   /* ESSL's _GEMMS: Strassen-Winograd, that many levels */
            q->pred = -1;
        } else if (parse_plan(tok, s0, q->plan)) {
            q->is_plan = 1;
            q->pred = plan_cost(cal, q->plan, s0);
        } else if (strcmp(tok, "dps48ops") || !square || n % 4) {
            printf("unknown method %s\n", tok);
            continue;
        } else {
            q->pred = -1;
        }
        errmod_t e = err_model(cal);
        q->perr = q->is_plan && e.ok ? plan_err(&e, q->plan, q->spad) : -1;
        nm++;
    }
    size_t wsz = 1024;
    for (int j = 0; j < nm; j++) {
        size_t w = ms[j].is_plan ? FN(padded_work)(ms[j].plan, s0, ms[j].spad)
                   : ms[j].gemms ? FN(gemms_work)(ms[j].gemms, s0.m, s0.k, s0.n)
                                 : (size_t)3 * 48 * (nn / 16);
        if (w > wsz) wsz = w;
    }
    free(cal);
    T *work = alloc_t(wsz * sizeof(T));
    memset(work, 0, wsz * sizeof(T));
#if defined(FMM_FLOAT) && defined(FMM_GPU)
    if (fmm_gpu_attach(A, na * sizeof(T)) || fmm_gpu_attach(B, nb * sizeof(T)) || fmm_gpu_attach(C, nn * sizeof(T)) ||
        fmm_gpu_attach(work, wsz * sizeof(T)))
        printf("# no GPU regions: the M leaves run on the GEMM\n");
#endif
    T **temps = NULL;
    int ntemps = max_temp() + 1;
    if (strstr(methods, "dps48ops")) {
        temps = calloc(ntemps, sizeof(T *));
        for (int k = 0; k < ntemps; k++) temps[k] = alloc_t((nn / 16) * sizeof(T));
    }
    FN(gemm)(s0, A, s0.k, B, s0.n, Cref, s0.n);
    double cmax = 0;
    for (size_t i = 0; i < nn; i++) cmax = fmax(cmax, fabs((double)Cref[i]));
    /* FMM_EXACT=1: also each method's error against an exact reference: in f32 the f64 product of
     * the same inputs, in f64 the compensated (double-double) product */
    const char *ex = getenv("FMM_EXACT");
    double *R64 = NULL, rmax64 = 0, err64[16] = {0};
    /* FMM_REFCACHE=DIR keeps each reference (it depends only on n, precision, distribution and
     * seed) for the other builds measuring the same inputs */
    const char *rc = getenv("FMM_REFCACHE");
    char refpath[1024] = "";
    if (ex && atoi(ex) && rc) {
        /* the key includes FMM_INPUT: without it a scaled run read the unscaled reference (2026-11-17) */
        const char *ik = inp && *inp ? inp : "plain";
        if (square) snprintf(refpath, sizeof refpath, "%s/ref_%s_%zu_%s_%s_%s.bin", rc, f64 ? "f64" : "f32", n,
                             (nrm && atoi(nrm)) ? "normal" : "uniform", seed ? seed : "0", ik);
        else snprintf(refpath, sizeof refpath, "%s/ref_%s_%zux%zux%zu_%s_%s_%s.bin", rc, f64 ? "f64" : "f32", s0.m, s0.k,
                      s0.n, (nrm && atoi(nrm)) ? "normal" : "uniform", seed ? seed : "0", ik);
    }
    int cached = 0;
    if (refpath[0]) {
        FILE *fr = fopen(refpath, "rb");
        if (fr) {
            R64 = alloc_t(nn * 8);
            cached = fread(R64, 8, nn, fr) == nn;
            fclose(fr);
            if (!cached) { free(R64); R64 = NULL; }
        }
    }
    if (ex && atoi(ex) && f64 && !cached) {
        R64 = alloc_t(nn * 8);
        double t0 = now();
        dd_gemm(s0.m, s0.k, s0.n, (const double *)A, (const double *)B, R64);
        printf("# compensated f64 reference in %.1f s\n", now() - t0);
    }
    if (ex && atoi(ex) && !f64 && !cached) {
        double *A64 = alloc_t(na * 8), *B64 = alloc_t(nb * 8);
        R64 = alloc_t(nn * 8);
        for (size_t i = 0; i < na; i++) A64[i] = A[i];
        for (size_t i = 0; i < nb; i++) B64[i] = B[i];
        cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)s0.m, (int)s0.n, (int)s0.k, 1.0, A64, (int)s0.k, B64,
                    (int)s0.n, 0.0, R64, (int)s0.n);
        free(A64); free(B64);
    }
    if (R64) {
        for (size_t i = 0; i < nn; i++) rmax64 = fmax(rmax64, fabs(R64[i]));
        if (refpath[0] && !cached) {
            FILE *fw = fopen(refpath, "wb");
            if (fw) { fwrite(R64, 8, nn, fw); fclose(fw); }
        }
    }
    /* with the exact reference, also the componentwise error max |C - C_exact| / (|A||B|), the
     * quantity the classical GEMM's error bound holds entry by entry */
    double *D64 = NULL, errcw[16] = {0};
    if (R64) {
        double *A64 = alloc_t(na * 8), *B64 = alloc_t(nb * 8);
        D64 = alloc_t(nn * 8);
        for (size_t i = 0; i < na; i++) A64[i] = fabs((double)A[i]);
        for (size_t i = 0; i < nb; i++) B64[i] = fabs((double)B[i]);
        cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)s0.m, (int)s0.n, (int)s0.k, 1.0, A64, (int)s0.k, B64,
                    (int)s0.n, 0.0, D64, (int)s0.n);
        free(A64); free(B64);
    }
    /* FMM_PRESCALE=1: every method multiplies diag(r) A diag(t) by diag(1/t) B diag(c) and unscales
     * C by diag(1/r), diag(1/c), all powers of two (exact): r and c bring each row of A and column
     * of B to a largest entry in [1,2) (outside scaling), t balances column l of A against row l of
     * B (inside scaling) */
    const char *pre = getenv("FMM_PRESCALE");
    const T *Ar = A, *Br = B;
    T *As = NULL, *Bs = NULL;
    int *er = NULL, *ec = NULL;
    FN(ps_mode) = pre ? atoi(pre) : 0;
    if (FN(ps_mode) >= 2) {
        FN(ps_copies) = alloc_t((na + nb) * sizeof(T));
        printf("# prescaled by the library: %s\n", FN(ps_mode) == 2 ? "separate passes" : "folded into the top level");
    }
    if (pre && atoi(pre) == 1) {
        er = calloc(s0.m, sizeof(int));
        ec = calloc(s0.n, sizeof(int));
        int *et = calloc(s0.k, sizeof(int));
        As = alloc_t(na * sizeof(T));
        Bs = alloc_t(nb * sizeof(T));
        for (size_t i = 0; i < s0.m; i++) {
            double mx = 0;
            for (size_t l = 0; l < s0.k; l++) mx = fmax(mx, fabs((double)A[i * s0.k + l]));
            er[i] = mx > 0 ? -ilogb(mx) : 0;
        }
        for (size_t j = 0; j < s0.n; j++) {
            double mx = 0;
            for (size_t l = 0; l < s0.k; l++) mx = fmax(mx, fabs((double)B[l * s0.n + j]));
            ec[j] = mx > 0 ? -ilogb(mx) : 0;
        }
        for (size_t i = 0; i < s0.m; i++)
            for (size_t l = 0; l < s0.k; l++) As[i * s0.k + l] = (T)ldexp((double)A[i * s0.k + l], er[i]);
        for (size_t l = 0; l < s0.k; l++)
            for (size_t j = 0; j < s0.n; j++) Bs[l * s0.n + j] = (T)ldexp((double)B[l * s0.n + j], ec[j]);
        for (size_t l = 0; l < s0.k; l++) {
            double ma = 0, mb = 0;
            for (size_t i = 0; i < s0.m; i++) ma = fmax(ma, fabs((double)As[i * s0.k + l]));
            for (size_t j = 0; j < s0.n; j++) mb = fmax(mb, fabs((double)Bs[l * s0.n + j]));
            et[l] = ma > 0 && mb > 0 ? (ilogb(mb) - ilogb(ma)) / 2 : 0;
            for (size_t i = 0; i < s0.m; i++) As[i * s0.k + l] = (T)ldexp((double)As[i * s0.k + l], et[l]);
            for (size_t j = 0; j < s0.n; j++) Bs[l * s0.n + j] = (T)ldexp((double)Bs[l * s0.n + j], -et[l]);
        }
        free(et);
        Ar = As;
        Br = Bs;
        printf("# prescaled: outside (rows of A, columns of B) and inside, by powers of two\n");
    }
    for (int j = 0; j < nm; j++) FN(run_method)(&ms[j], s0, Ar, Br, C, work, temps, NULL);  /* warm-up */
    double times[16][32];
    FN(split_t) sp[16];
    memset(sp, 0, sizeof sp);
    double err[16] = {0};
    uint64_t hashes[16] = {0};
    for (int q = 0; q < reps; q++)          /* rounds: drift hits every method alike */
        for (int j = 0; j < nm; j++) {
            double t = now();
            FN(run_method)(&ms[j], s0, Ar, Br, C, work, temps, &sp[j]);
            times[j][q] = now() - t;
            if (q == reps - 1) {
                if (er)
                    for (size_t i = 0; i < s0.m; i++)
                        for (size_t c = 0; c < s0.n; c++)
                            C[i * s0.n + c] = (T)ldexp((double)C[i * s0.n + c], -er[i] - ec[c]);
                for (size_t i = 0; i < nn; i++) err[j] = fmax(err[j], fabs((double)C[i] - (double)Cref[i]));
                if (R64)
                    for (size_t i = 0; i < nn; i++) err64[j] = fmax(err64[j], fabs((double)C[i] - R64[i]));
                if (D64)
                    for (size_t i = 0; i < nn; i++)
                        if (D64[i] > 0) errcw[j] = fmax(errcw[j], fabs((double)C[i] - R64[i]) / D64[i]);
                uint64_t h = 1469598103934665603ull;   /* FNV-1a over C's bytes */
                for (size_t i = 0; i < nn * sizeof(T); i++) h = (h ^ ((const unsigned char *)C)[i]) * 1099511628211ull;
                hashes[j] = h;
            }
        }
    double tclass = 0;
    for (int j = 0; j < nm; j++) {
        double *tj = times[j];
        for (int a = 0; a < reps; a++)
            for (int b = a + 1; b < reps; b++)
                if (tj[b] < tj[a]) { double x = tj[a]; tj[a] = tj[b]; tj[b] = x; }
        double med = tj[reps / 2], best = tj[0];
        if (!strcmp(ms[j].name, "classical")) tclass = med;
        printf("%-10s %s %s  min %8.4f s  med %8.4f s  %7.1f GFLOP/s(2mkn)  speedup %5.3f  "
               "relerr %.2e  split L %.3f R %.3f gemm %.3f P %.3f",
               ms[j].name, shp, f64 ? "f64" : "f32", best, med, 2.0 * s0.m * s0.k * (double)s0.n / med / 1e9,
               tclass > 0 ? tclass / med : 0.0, err[j] / cmax, sp[j].tL / reps, sp[j].tR / reps,
               sp[j].tG / reps, sp[j].tP / reps);
        if (ms[j].is_plan) {
            char ps[128];
            plan_str(ms[j].plan, ps, sizeof ps);
            printf("  plan %s", ps);
            if (!shape_eq(ms[j].spad, s0)) printf("@%zux%zux%zu", ms[j].spad.m, ms[j].spad.k, ms[j].spad.n);
            if (ms[j].pred > 0) printf("  pred %.3f s (%+.1f%%)", ms[j].pred, 100 * (ms[j].pred / med - 1));
            if (ms[j].perr > 0) printf("  perr %.2e", ms[j].perr);
        }
        if (R64) printf("  err64 %.2e", err64[j] / rmax64);
        if (D64) printf("  cw %.2e", errcw[j]);
        if (getenv("FMM_HASH")) printf("  hash %016llx", (unsigned long long)hashes[j]);
        printf("\n");
        fflush(stdout);
    }
    if (temps) {
        for (int k = 0; k < ntemps; k++) free(temps[k]);
        free(temps);
    }
    free(R64); free(D64); free(As); free(Bs); free(er); free(ec); free(FN(ps_copies));
    FN(ps_copies) = NULL;
#if defined(FMM_FLOAT) && defined(FMM_GPU)
    fmm_gpu_detach_all();
#endif
    free(A); free(B); free(C); free(Cref); free(work);
}

#undef FN
#undef CAT
#undef CAT_
