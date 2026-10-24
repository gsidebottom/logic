/* bench_impl.h: one precision of the fast matrix multiplication benchmark; included by
 * bench_fmm.c with T (float or double), SUF (f or d) and GEMM (cblas_sgemm or cblas_dgemm).
 * Matrices are row-major n x n; block (k / g, k % g) of a g x g grid starts at
 * X + (k / g) * m * n + (k % g) * m with leading dimension n. */

#define CAT_(a, b) a##b
#define CAT(a, b) CAT_(a, b)
#define FN(name) CAT(name, SUF)

typedef void (*FN(kern_t))(size_t, size_t, size_t, const T *const *, T *const *, size_t, size_t);

static void FN(gemm)(size_t m, const T *A, size_t lda, const T *B, size_t ldb, T *C, size_t ldc) {
    GEMM(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)m, (int)m, (int)m, (T)1, A, (int)lda, B,
         (int)ldb, (T)0, C, (int)ldc);
}

/* classical multiplication as g^3 block GEMMs of size n/g accumulating into C: the fair
 * classical baseline when the library runs faster on blocks than on one big call */
static void FN(classical_blocked)(int g, size_t n, const T *A, size_t lda, const T *B, size_t ldb, T *C,
                                  size_t ldc) {
    size_t m = n / g;
    for (int i = 0; i < g; i++)
        for (int j = 0; j < g; j++)
            for (int k = 0; k < g; k++)
                GEMM(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)m, (int)m, (int)m, (T)1,
                     A + (size_t)i * m * lda + (size_t)k * m, (int)lda, B + (size_t)k * m * ldb + (size_t)j * m,
                     (int)ldb, k ? (T)1 : (T)0, C + (size_t)i * m * ldc + (size_t)j * m, (int)ldc);
}

/* a fused pass, rows of the blocks split over the cores */
static void FN(pass)(FN(kern_t) k, size_t m, size_t ld_in, size_t ld_out, const T *const *in, T *const *out) {
    size_t chunks = 64, step = (m + chunks - 1) / chunks;
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
        size_t r0 = ch * step, r1 = r0 + step < m ? r0 + step : m;
        if (r0 < r1) k(m, ld_in, ld_out, in, out, r0, r1);
    });
}

typedef struct {
    double tL, tR, tG, tP;
} FN(split_t);

/* the three kernels of a fused level type */
static void FN(kernels)(int lv, FN(kern_t) k[3]) {
    if (lv == LV_SW) { k[0] = FN(sw_L_); k[1] = FN(sw_R_); k[2] = FN(sw_P_); }
    else if (lv == LV_D48) { k[0] = FN(dps48_L_); k[1] = FN(dps48_R_); k[2] = FN(dps48_P_); }
    else { k[0] = FN(sw2_L_); k[1] = FN(sw2_R_); k[2] = FN(sw2_P_); }
}

/* the r products of a level as k single-threaded GEMM streams taking products in turn */
static void FN(gemm_streams)(int r, size_t m, T *const *S, T *const *Tt, T *const *M, int k) {
    atomic_int next = 0;
    atomic_int *pn = &next;
    dispatch_apply((size_t)k, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t w) {
        (void)w;
        enum BLAS_THREADING old = BLASGetThreading();
        BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
        for (int q; (q = atomic_fetch_add(pn, 1)) < r;) FN(gemm)(m, S[q], m, Tt[q], m, M[q], m);
        BLASSetThreading(old);
    });
}

/* the r products of a level: the first r - j as k single-threaded GEMM streams taking products
 * in turn, the last j by w NEON threads, all at once.  A NEON task is a slab of FMM_NEON_SLAB
 * rows of a product (default 0: the whole product; each task packs all of B again, so small
 * slabs multiply the traffic through the L2 the SME units share).  The packing buffers are
 * allocated once, for the largest m seen. */
static void FN(gemm_hybrid)(int r, size_t m, T *const *S, T *const *Tt, T *const *M, int k, int j, int w) {
    static T *pa[64], *pb[64];
    static size_t cap;
    const char *e = getenv("FMM_NEON_SLAB");
    size_t slab = e ? (size_t)atol(e) : 0;
    if (slab == 0 || slab > m) slab = m;
    if (m > cap) {
        for (int q = 0; q < 64; q++) {
            free(pa[q]); free(pb[q]);
            pa[q] = alloc_t(m * NEON_KC * sizeof(T) + 64);
            pb[q] = alloc_t(m * NEON_KC * sizeof(T) + 64);
        }
        cap = m;
    }
    if (j > r) j = r;
    if (w > 64) w = 64;
    int slabs = (int)((m + slab - 1) / slab), tasks = j * slabs;
    atomic_int next = 0, ntask = 0;
    atomic_int *pn = &next, *pt = &ntask;
    dispatch_apply((size_t)(k + w), dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t id) {
        if ((int)id < k) {
            enum BLAS_THREADING old = BLASGetThreading();
            BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
            for (int q; (q = atomic_fetch_add(pn, 1)) < r - j;) FN(gemm)(m, S[q], m, Tt[q], m, M[q], m);
            BLASSetThreading(old);
        } else {
            T *a = pa[id - k], *b = pb[id - k];
            for (int t; (t = atomic_fetch_add(pt, 1)) < tasks;) {
                int q = r - j + t / slabs;
                size_t r0 = (size_t)(t % slabs) * slab, r1 = r0 + slab < m ? r0 + slab : m;
                NEON_GEMM_ROWS(m, S[q], m, Tt[q], m, M[q], m, r0, r1, a, b);
            }
        }
    });
}

/* C = A B at size n by a plan (plan[0] the top level); work holds plan_work(plan, n) elements.
 * A fused level splits A, B, C into a g x g grid of blocks of m = n / g, writes the r factors
 * S_k and T_k (one pass per side), computes M_k = S_k T_k by the rest of the plan (the scratch
 * below this level reused product after product) and writes C from the M_k (one pass).  GEMM
 * time is counted where the GEMMs run, pass time at every level. */
static void FN(exec)(const int *plan, size_t n, const T *A, size_t lda, const T *B, size_t ldb, T *C,
                     size_t ldc, T *work, FN(split_t) *sp) {
    int lv = PLV(plan[0]);
    if (lv == LV_NONE) return;
    if (lv_leaf(lv)) {
        double t = now();
        if (lv == LV_G) FN(gemm)(n, A, lda, B, ldb, C, ldc);
        else FN(classical_blocked)(lv_grid(lv), n, A, lda, B, ldb, C, ldc);
        if (sp) sp->tG += now() - t;
        return;
    }
    int g = lv_grid(lv), r = lv_rank(lv);
    FN(kern_t) k[3];
    FN(kernels)(lv, k);
    size_t m = n / g;
    const T *Ab[16], *Bb[16];
    T *Cb[16], *S[64], *Tt[64], *M[64];
    for (int q = 0; q < g * g; q++) {
        Ab[q] = A + (q / g) * m * lda + (q % g) * m;
        Bb[q] = B + (q / g) * m * ldb + (q % g) * m;
        Cb[q] = C + (q / g) * m * ldc + (q % g) * m;
    }
    /* scratch blocks m*m + pad apart: with pad 0 every block starts at the same offset modulo
     * any power of two up to m*m, so element c of every stream maps to one cache set */
    size_t bs = m * m + fmm_pad();
    for (int q = 0; q < r; q++) {
        S[q] = work + (size_t)q * bs;
        Tt[q] = work + (size_t)(r + q) * bs;
        M[q] = work + (size_t)(2 * r + q) * bs;
    }
    T *deeper = work + (size_t)3 * r * bs;
    double t0 = now();
    FN(pass)(k[0], m, lda, m, Ab, S);
    double t1 = now();
    FN(pass)(k[1], m, ldb, m, Bb, Tt);
    double t2 = now();
    if (sp) {
        sp->tL += t1 - t0;
        sp->tR += t2 - t1;
    }
    if (PLV(plan[1]) == LV_G && PNE(plan[1]) > 0) {
        double t = now();
        FN(gemm_hybrid)(r, m, S, Tt, M, PST(plan[1]), PNE(plan[1]), fmm_neon_threads());
        if (sp) sp->tG += now() - t;
    } else if (PLV(plan[1]) == LV_G && PST(plan[1]) > 0) {
        double t = now();
        FN(gemm_streams)(r, m, S, Tt, M, PST(plan[1]));
        if (sp) sp->tG += now() - t;
    } else {
        for (int q = 0; q < r; q++) FN(exec)(plan + 1, m, S[q], m, Tt[q], m, M[q], m, deeper, sp);
    }
    double t3 = now();
    FN(pass)(k[2], m, m, ldc, (const T *const *)M, Cb);
    if (sp) sp->tP += now() - t3;
}

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

/* calibration timing: caches evicted before each run; repeated until 3 runs and 0.3 s, or 2 s,
 * or 15 runs; the median (the lower middle for an even count) */
static double FN(time_plan)(const int *plan, size_t n, const T *A, const T *B, T *C, T *work) {
    double ts[15], tot = 0;
    int cnt = 0;
    while (cnt < 15 && tot < 2.0 && !(cnt >= 3 && tot >= 0.3)) {
        evict();
        double t = now();
        FN(exec)(plan, n, A, n, B, n, C, n, work, NULL);
        ts[cnt] = now() - t;
        tot += ts[cnt++];
    }
    for (int a = 0; a < cnt; a++)
        for (int b = a + 1; b < cnt; b++)
            if (ts[b] < ts[a]) { double x = ts[a]; ts[a] = ts[b]; ts[b] = x; }
    return ts[(cnt - 1) / 2];
}

/* one fused level of type lv with blocks m and GEMM products (as `streams` streams), caches
 * evicted before each run, repeated as in time_plan: the medians of its pass time and of its
 * GEMM time per product */
static void FN(time_level)(int lv, size_t m, int streams, const T *A, const T *B, T *C, T *work,
                           double *passes, double *gemm) {
    int plan[2] = {lv, LV_G | (streams << 8)};
    size_t n = m * lv_grid(lv);
    double tp[15], tg[15], tot = 0;
    int cnt = 0;
    while (cnt < 15 && tot < 2.0 && !(cnt >= 3 && tot >= 0.3)) {
        FN(split_t) sp = {0};
        evict();
        double t = now();
        FN(exec)(plan, n, A, n, B, n, C, n, work, &sp);
        tot += now() - t;
        tp[cnt] = sp.tL + sp.tR + sp.tP;
        tg[cnt++] = sp.tG / lv_rank(lv);
    }
    for (int a = 0; a < cnt; a++)
        for (int b = a + 1; b < cnt; b++) {
            if (tp[b] < tp[a]) { double x = tp[a]; tp[a] = tp[b]; tp[b] = x; }
            if (tg[b] < tg[a]) { double x = tg[a]; tg[a] = tg[b]; tg[b] = x; }
        }
    *passes = tp[(cnt - 1) / 2];
    *gemm = tg[(cnt - 1) / 2];
}

/* measure the entries plan_best needs for n that the cache lacks, and save the cache; A, B, C
 * hold n*n elements, smaller problems use their first m*m as contiguous m x m matrices */
static void FN(calibrate)(calib_t *c, size_t n, const T *A, const T *B, T *C) {
    calib_t need;
    memset(&need, 0, sizeof need);
    calib_need(&need, n);
    size_t wmax = 0;
    int missing = 0, todo[CALIB_MAX];
    for (int i = 0; i < need.n; i++) {
        int kind = need.kind[i];
        size_t m = need.m[i];
        todo[i] = 0;
        if (kind >= K_GIN) continue;
        todo[i] = calib_get(c, kind, m) < 0;
        for (int k = 0; !lv_leaf(kind) && k < NSTREAMS; k++)
            if (calib_get(c, kind_gin(kind, STREAMS[k]), m) < 0) todo[i] = 1;
        if (!todo[i]) continue;
        missing++;
        int plan[2] = {kind, LV_G};
        size_t w = plan_work(plan, m * lv_grid(kind));
        if (w > wmax) wmax = w;
    }
    if (!missing) return;
    printf("# calibrating %d entries (%s)\n", missing, sizeof(T) == 4 ? "f32" : "f64");
    T *work = alloc_t((wmax + 16) * sizeof(T));
    memset(work, 0, (wmax + 16) * sizeof(T));
    for (int i = 0; i < need.n; i++) {
        int kind = need.kind[i];
        size_t m = need.m[i];
        if (!todo[i]) continue;
        if (lv_leaf(kind)) {
            int plan[1] = {kind};
            double t = FN(time_plan)(plan, m, A, B, C, work);
            calib_put(c, kind, m, t);
            printf("#   %-4s m=%-6zu %.6f s\n", kind_name(kind), m, t);
        } else {
            printf("#   %-4s m=%-6zu", kind_name(kind), m);
            for (int k = 0; k < NSTREAMS; k++) {
                double tp, tg;
                FN(time_level)(kind, m, STREAMS[k], A, B, C, work, &tp, &tg);
                if (k == 0) {
                    calib_put(c, kind, m, tp);
                    printf(" %.6f s ", tp);
                }
                calib_put(c, kind_gin(kind, STREAMS[k]), m, tg);
                printf("  %s %.6f", kind_name(kind_gin(kind, STREAMS[k])), tg);
                fflush(stdout);
            }
            printf("\n");
        }
        fflush(stdout);
    }
    free(work);
    calib_save(c, sizeof(T) == 8);
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
        if (!strcmp(tok, "auto")) {
            FN(calibrate)(cal, n, A, B, C);
            if (plan_best(cal, n, q->plan) < 0) { printf("auto: nothing calibrated for n=%zu\n", n); continue; }
            q->is_plan = 1;
            char ps[128];
            plan_str(q->plan, ps, sizeof ps);
            printf("# auto n=%zu %s: plan %s, predicted %.3f s\n", n, f64 ? "f64" : "f32", ps,
                   plan_cost(cal, q->plan, n));
        } else if (parse_plan(tok, n, q->plan)) {
            q->is_plan = 1;
        } else if (strcmp(tok, "dps48ops") || n % 4) {
            printf("unknown method %s\n", tok);
            continue;
        }
        q->pred = q->is_plan ? plan_cost(cal, q->plan, n) : -1;
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
            if (q == reps - 1)
                for (size_t i = 0; i < nn; i++) err[j] = fmax(err[j], fabs((double)C[i] - (double)Cref[i]));
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
        }
        printf("\n");
        fflush(stdout);
    }
    if (temps) {
        for (int k = 0; k < ntemps; k++) free(temps[k]);
        free(temps);
    }
    free(A); free(B); free(C); free(Cref); free(work);
}

#undef FN
#undef CAT
#undef CAT_
