/* bench_impl.h: one precision of the benchmark driver (bench_fmm.c), on top of the library's
 * fmm_impl.h: the 48-scheme op by op, the GEMM timing probe, the plan table and the timed
 * comparison of methods. */

#define CAT_(a, b) a##b
#define CAT(a, b) CAT_(a, b)
#define FN(name) CAT(name, SUF)

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
    for (int k = 0; k < r; k++) FN(gemm)(m, S[k], m, Tt[k], m, M[k], m);
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
    size_t wsz = plan_work(top, n);
    T *work = alloc_t(wsz * sizeof(T));
    memset(work, 0, wsz * sizeof(T));
    for (size_t m = 256; 4 * m <= n; m *= 2) {
        int pg[2] = {LV_G, LV_NONE};
        double single = FN(time_plan)(pg, m, A, B, C, work);
        size_t bs = m * m + fmm_pad();
        int K = (int)(wsz / (3 * bs));
        if (K > 48) K = 48;
        double ts[9], tl[9];
        for (int q = 0; q < 9; q++) {
            evict();
            double t = now();
            for (int k = 0; k < K; k++)
                FN(gemm)(m, work + (size_t)k * bs, m, work + (size_t)(K + k) * bs, m, work + (size_t)(2 * K + k) * bs, m);
            ts[q] = (now() - t) / K;
            FN(split_t) sp = {0};
            evict();
            FN(exec)(top, 4 * m, A, 4 * m, B, 4 * m, C, 4 * m, work, &sp);
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
    FN(calibrate)(cal, n, A, B, C);
    static const char *NAMED[] = {"classical", "blk2", "sw1", "sw2rec", "sw3rec", "sw4rec", "dps48",
                                  "dps48sw", "dps48x2"};
    for (size_t sz = n; sz >= 1024 && sz % 2 == 0; sz /= 2) {
        int plan[PLAN_MAX];
        char ps[128];
        double best = plan_best(cal, sz, plan);
        if (best < 0) break;
        plan_str(plan, ps, sizeof ps);
        printf("n=%-6zu %s  best %-16s %8.4f s ", sz, f64 ? "f64" : "f32", ps, best);
        for (size_t i = 0; i < sizeof NAMED / sizeof NAMED[0]; i++) {
            int p2[PLAN_MAX];
            double t = parse_plan(NAMED[i], sz, p2) ? plan_cost(cal, p2, sz) : -1;
            if (t > 0) printf(" %s %.4f", NAMED[i], t);
        }
        printf("\n");
        static ranked_t rk[4096];
        int cnt = plan_enum(cal, sz, rk, 4096);
        printf("         top:");
        for (int i = 0; i < cnt && i < 6; i++) {
            plan_str(rk[i].plan, ps, sizeof ps);
            printf(" %s %.4f%s", ps, rk[i].t, i + 1 < cnt && i < 5 ? "," : "");
        }
        printf("  (%d plans)\n", cnt);
        errmod_t e = err_model(cal);
        if (e.ok) {
            printf("         error growth over classical: best %.1f (pred. error %.1e);", plan_growth(&e, plan),
                   plan_err(&e, plan, sz));
            static const double BUDGET[] = {16, 8, 4, 2};
            for (int b = 0; b < 4; b++) {
                int pb[PLAN_MAX];
                double t = plan_best_budget(cal, sz, BUDGET[b], pb);
                if (t < 0) continue;
                plan_str(pb, ps, sizeof ps);
                printf(" <=%g: %s %.4f s%s", BUDGET[b], ps, t, b < 3 ? "," : "");
            }
            printf("\n");
        }
    }
    if (n >= N_E) {
        errmod_t e = err_model(cal);
        if (e.ok)
            printf("# error model: classical scale %.2e at n = %d (x sqrt(n / %d)); factor per level SW %.2f, "
                   "D48 %.2f\n", e.base, N_E, N_E, e.f[LV_SW], e.f[LV_D48]);
    }
    free(cal);
    free(A); free(B); free(C);
}

static void FN(run_method)(const meth_t *q, size_t n, const T *A, const T *B, T *C, T *work, T **temps,
                           FN(split_t) *sp) {
    if (q->is_plan) FN(exec)(q->plan, n, A, n, B, n, C, n, work, sp);
    else FN(dps48_opbyop)(n, A, B, C, work, temps, sp);
}

static void FN(bench)(size_t n, const char *methods, int reps) {
    size_t nn = n * n;
    int f64 = sizeof(T) == 8;
    T *A = alloc_t(nn * sizeof(T)), *B = alloc_t(nn * sizeof(T)), *C = alloc_t(nn * sizeof(T)),
      *Cref = alloc_t(nn * sizeof(T));
    uint64_t s = 0x9e3779b97f4a7c15ull;
    for (size_t i = 0; i < nn; i++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        A[i] = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        B[i] = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
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
        if (!strncmp(tok, "auto", 4) && (tok[4] == 0 || tok[4] == ':')) {
            double gmax = tok[4] == ':' ? atof(tok + 5) : fmm_max_growth();
            FN(calibrate)(cal, n, A, B, C);
            if (plan_best_budget(cal, n, gmax, q->plan) < 0) {
                printf("%s: nothing calibrated for n=%zu\n", tok, n);
                continue;
            }
            q->is_plan = 1;
            char ps[128];
            plan_str(q->plan, ps, sizeof ps);
            printf("# %s n=%zu %s: plan %s, predicted %.3f s\n", tok, n, f64 ? "f64" : "f32", ps,
                   plan_cost(cal, q->plan, n));
        } else if (parse_plan(tok, n, q->plan)) {
            q->is_plan = 1;
        } else if (strcmp(tok, "dps48ops") || n % 4) {
            printf("unknown method %s\n", tok);
            continue;
        }
        q->pred = q->is_plan ? plan_cost(cal, q->plan, n) : -1;
        errmod_t e = err_model(cal);
        q->perr = q->is_plan && e.ok ? plan_err(&e, q->plan, n) : -1;
        nm++;
    }
    size_t wsz = 1024;
    for (int j = 0; j < nm; j++) {
        size_t w = ms[j].is_plan ? plan_work(ms[j].plan, n) : (size_t)3 * 48 * (nn / 16);
        if (w > wsz) wsz = w;
    }
    free(cal);
    T *work = alloc_t(wsz * sizeof(T));
    memset(work, 0, wsz * sizeof(T));
    T **temps = NULL;
    int ntemps = max_temp() + 1;
    if (strstr(methods, "dps48ops")) {
        temps = calloc(ntemps, sizeof(T *));
        for (int k = 0; k < ntemps; k++) temps[k] = alloc_t((nn / 16) * sizeof(T));
    }
    FN(gemm)(n, A, n, B, n, Cref, n);
    double cmax = 0;
    for (size_t i = 0; i < nn; i++) cmax = fmax(cmax, fabs((double)Cref[i]));
    /* FMM_EXACT=1 in f32: also each method's error against an f64 product of the same inputs */
    const char *ex = getenv("FMM_EXACT");
    double *R64 = NULL, rmax64 = 0, err64[16] = {0};
    if (ex && atoi(ex) && !f64) {
        double *A64 = alloc_t(nn * 8), *B64 = alloc_t(nn * 8);
        R64 = alloc_t(nn * 8);
        for (size_t i = 0; i < nn; i++) { A64[i] = A[i]; B64[i] = B[i]; }
        cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)n, (int)n, (int)n, 1.0, A64, (int)n, B64, (int)n,
                    0.0, R64, (int)n);
        for (size_t i = 0; i < nn; i++) rmax64 = fmax(rmax64, fabs(R64[i]));
        free(A64); free(B64);
    }
    for (int j = 0; j < nm; j++) FN(run_method)(&ms[j], n, A, B, C, work, temps, NULL);  /* warm-up */
    double times[16][32];
    FN(split_t) sp[16];
    memset(sp, 0, sizeof sp);
    double err[16] = {0};
    for (int q = 0; q < reps; q++)          /* rounds: drift hits every method alike */
        for (int j = 0; j < nm; j++) {
            double t = now();
            FN(run_method)(&ms[j], n, A, B, C, work, temps, &sp[j]);
            times[j][q] = now() - t;
            if (q == reps - 1) {
                for (size_t i = 0; i < nn; i++) err[j] = fmax(err[j], fabs((double)C[i] - (double)Cref[i]));
                if (R64)
                    for (size_t i = 0; i < nn; i++) err64[j] = fmax(err64[j], fabs((double)C[i] - R64[i]));
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
        printf("%-10s n=%-6zu %s  min %8.3f s  med %8.3f s  %7.1f GFLOP/s(2n^3)  speedup %5.3f  "
               "relerr %.2e  split L %.3f R %.3f gemm %.3f P %.3f",
               ms[j].name, n, f64 ? "f64" : "f32", best, med, 2.0 * n * n * (double)n / med / 1e9,
               tclass > 0 ? tclass / med : 0.0, err[j] / cmax, sp[j].tL / reps, sp[j].tR / reps,
               sp[j].tG / reps, sp[j].tP / reps);
        if (ms[j].is_plan) {
            char ps[128];
            plan_str(ms[j].plan, ps, sizeof ps);
            printf("  plan %s", ps);
            if (ms[j].pred > 0) printf("  pred %.3f s (%+.1f%%)", ms[j].pred, 100 * (ms[j].pred / med - 1));
            if (ms[j].perr > 0) printf("  perr %.2e", ms[j].perr);
        }
        if (R64) printf("  err64 %.2e", err64[j] / rmax64);
        printf("\n");
        fflush(stdout);
    }
    if (temps) {
        for (int k = 0; k < ntemps; k++) free(temps[k]);
        free(temps);
    }
    free(R64);
    free(A); free(B); free(C); free(Cref); free(work);
}

#undef FN
#undef CAT
#undef CAT_
