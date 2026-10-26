/* fmm_impl.h: one precision of the fast matrix multiplication library (fmm.c): the plan
 * executor (fused passes, GEMM streams, pipelines), the calibration and the entry points;
 * included by fmm.c with T (float or double), SUF (f or d), GEMM (cblas_sgemm or cblas_dgemm)
 * and NEON_GEMM_ROWS.  Matrices are row-major n x n; block (k / g, k % g) of a g x g grid starts
 * at X + (k / g) * m * ld + (k % g) * m with leading dimension ld. */

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
#ifdef FMM_FLOAT
    else if (lv == LV_D48 && fmm_f64pass()) { k[0] = dps48_L_fd; k[1] = dps48_R_fd; k[2] = dps48_P_fd; }
#endif
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

/* the r products of a level, each a level Y (py[0]) over GEMM streams (py[1]), pipelined: in
 * step q the streams compute the products of sub-problem q while w pass threads write the
 * result of sub-problem q - 1 (Y's P pass) and the factors of sub-problem q + 1 (Y's L and R
 * passes).  Y's scratch is double-buffered (sets q % 2): IN(q + 1) writes the S and T of the set
 * GEMM(q - 1) has finished reading, OUT(q - 1) reads its M, which GEMM(q + 1) overwrites only in
 * the next step.  Few pass threads: streaming passes starve the SME units (probe_overlap). */
typedef struct {
    const T *in[2][16];         /* Y's input blocks of sub-problems: A side, B side */
    T *out[16];
    T *S[2][64], *Tt[2][64], *M[2][64];
} FN(pipe_t);

/* background passes: up to three passes in row chunks, which the pass threads of a pipeline run
 * when their own passes are done while the GEMMs of the step still run; the rest is drained
 * after the pipeline */
typedef struct {
    int n, nch;
    FN(kern_t) k[3];
    size_t mb[3], ldi[3], ldo[3];
    const T *in[3][64];
    T *out[3][64];
    atomic_int next;
} FN(bg_t);

static void FN(bg_add)(FN(bg_t) *bg, FN(kern_t) k, size_t mb, size_t ldi, size_t ldo, const T *const *in, int nin,
                       T *const *out, int nout) {
    int p = bg->n++;
    bg->k[p] = k;
    bg->mb[p] = mb;
    bg->ldi[p] = ldi;
    bg->ldo[p] = ldo;
    for (int i = 0; i < nin; i++) bg->in[p][i] = in[i];
    for (int i = 0; i < nout; i++) bg->out[p][i] = out[i];
}

/* run the next background chunk; 0 when none is left */
static int FN(bg_chunk)(FN(bg_t) *bg) {
    int t = atomic_fetch_add(&bg->next, 1);
    if (t >= bg->n * bg->nch) return 0;
    int p = t / bg->nch, c = t % bg->nch;
    size_t step = (bg->mb[p] + bg->nch - 1) / bg->nch, r0 = (size_t)c * step,
           r1 = r0 + step < bg->mb[p] ? r0 + step : bg->mb[p];
    if (r0 < r1) bg->k[p](bg->mb[p], bg->ldi[p], bg->ldo[p], bg->in[p], bg->out[p], r0, r1);
    return 1;
}

static void FN(bg_drain)(FN(bg_t) *bg) {
    dispatch_apply(16, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t i) {
        (void)i;
        while (FN(bg_chunk)(bg)) {}
    });
}

static void FN(pipeline)(const int *py, size_t m, int r, T *const *SX, T *const *TX, T *const *MX, T *work,
                         FN(split_t) *sp, int w, FN(bg_t) *bg) {
    int ly = PLV(py[0]), gy = lv_grid(ly), ry = lv_rank(ly), k = PST(py[1]);
    size_t my = m / gy, bs = my * my + fmm_pad(), set = (size_t)3 * ry * bs;
    FN(kern_t) ky[3];
    FN(kernels)(ly, ky);
    FN(kern_t) kL = ky[0], kR = ky[1], kP = ky[2];  /* blocks cannot capture arrays */
    FN(pipe_t) pp;
    FN(pipe_t) *P = &pp;
    for (int b = 0; b < 2; b++)
        for (int j = 0; j < ry; j++) {
            P->S[b][j] = work + b * set + (size_t)j * bs;
            P->Tt[b][j] = work + b * set + (size_t)(ry + j) * bs;
            P->M[b][j] = work + b * set + (size_t)(2 * ry + j) * bs;
        }
    int nch = 16;                               /* row chunks per pass */
    size_t step = (my + nch - 1) / nch;
    double t0 = now();
    for (int q = -1; q <= r; q++) {
        int qo = q - 1, qi = q + 1, gq = q >= 0 && q < r;
        int have_out = qo >= 0, have_in = qi < r;
        /* block pointers of sub-problem qi's inputs (blocks of SX[qi], TX[qi]) and qo's output */
        T *in_s[16], *in_t[16], *out_c[16];
        for (int b = 0; b < gy * gy; b++) {
            size_t off = (size_t)(b / gy) * my * m + (size_t)(b % gy) * my;
            if (have_in) { in_s[b] = SX[qi] + off; in_t[b] = TX[qi] + off; }
            if (have_out) out_c[b] = MX[qo] + off;
        }
        int ntask = (have_out ? nch : 0) + (have_in ? 2 * nch : 0);
        atomic_int next_p = 0, next_g = 0;
        atomic_int *pnp = &next_p, *png = &next_g;
        const T *const *ins = (const T *const *)in_s, *const *int_ = (const T *const *)in_t;
        T *const *outc = out_c;
        int si = qi & 1, sg = q & 1, so = qo & 1;
        atomic_int gemm_active = gq ? k : 0;
        atomic_int *pga = &gemm_active;
        dispatch_apply((size_t)(k + w), dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t id) {
            if ((int)id < k) {
                if (!gq) return;
                enum BLAS_THREADING old = BLASGetThreading();
                BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
                for (int j; (j = atomic_fetch_add(png, 1)) < ry;)
                    FN(gemm)(my, P->S[sg][j], my, P->Tt[sg][j], my, P->M[sg][j], my);
                BLASSetThreading(old);
                atomic_fetch_sub(pga, 1);
            } else {
                for (int t; (t = atomic_fetch_add(pnp, 1)) < ntask;) {
                    int pass = have_out ? (t < nch ? 2 : (t < 2 * nch ? 0 : 1)) : (t < nch ? 0 : 1);
                    size_t c = (size_t)(t % nch), r0 = c * step, r1 = r0 + step < my ? r0 + step : my;
                    if (r0 >= r1) continue;
                    if (pass == 0) kL(my, m, my, ins, P->S[si], r0, r1);
                    else if (pass == 1) kR(my, m, my, int_, P->Tt[si], r0, r1);
                    else kP(my, my, m, (const T *const *)P->M[so], outc, r0, r1);
                }
                if (bg)                                 /* the level above's passes, while GEMMs run */
                    while (atomic_load(pga) > 0 && FN(bg_chunk)(bg)) {}
            }
        });
    }
    if (sp) sp->tG += now() - t0;   /* the pipeline: GEMMs with the passes below hidden in them */
}

/* the r products of a level, each a pipelined level Z (pz[0]) over Y (pz[1]) and GEMM streams
 * (pz[2]): Z's own passes run in the background of the neighbouring products' pipelines.  While
 * product i's pipeline runs, its pass threads, when free, write product i - 1's result (Z's P
 * pass) and the factors of product i + 1 (Z's L and R passes); what is left runs on all cores
 * before product i + 1.  Z's scratch is double-buffered (sets i % 2), the pipelines' shared. */
static void FN(pipeline2)(const int *pz, size_t m, int r, T *const *SX, T *const *TX, T *const *MX, T *work,
                          FN(split_t) *sp) {
    int lz = PLV(pz[0]), gz = lv_grid(lz), rz = lv_rank(lz);
    int w = PPW(pz[0]) ? PPW(pz[0]) : fmm_pass_threads();
    size_t mz = m / gz, bs = mz * mz + fmm_pad(), set = (size_t)3 * rz * bs;
    FN(kern_t) kz[3];
    FN(kernels)(lz, kz);
    T *SZ[2][64], *TZ[2][64], *MZ[2][64];
    for (int b = 0; b < 2; b++)
        for (int j = 0; j < rz; j++) {
            SZ[b][j] = work + b * set + (size_t)j * bs;
            TZ[b][j] = work + b * set + (size_t)(rz + j) * bs;
            MZ[b][j] = work + b * set + (size_t)(2 * rz + j) * bs;
        }
    T *below = work + 2 * set;
#define ZBLK(X, q, b) ((X)[q] + (size_t)((b) / gz) * mz * m + (size_t)((b) % gz) * mz)
    double t0 = now();
    const T *ia[16], *ib[16];
    T *oc[16];
    for (int b = 0; b < gz * gz; b++) { ia[b] = ZBLK(SX, 0, b); ib[b] = ZBLK(TX, 0, b); }
    FN(pass)(kz[0], mz, m, mz, ia, SZ[0]);
    FN(pass)(kz[1], mz, m, mz, ib, TZ[0]);
    for (int i = 0; i < r; i++) {
        FN(bg_t) bgv;
        FN(bg_t) *bg = &bgv;
        bg->n = 0;
        bg->nch = 64;
        atomic_init(&bg->next, 0);
        if (i >= 1) {
            for (int b = 0; b < gz * gz; b++) oc[b] = ZBLK(MX, i - 1, b);
            FN(bg_add)(bg, kz[2], mz, mz, m, (const T *const *)MZ[(i - 1) & 1], rz, oc, gz * gz);
        }
        if (i + 1 < r) {
            for (int b = 0; b < gz * gz; b++) { ia[b] = ZBLK(SX, i + 1, b); ib[b] = ZBLK(TX, i + 1, b); }
            FN(bg_add)(bg, kz[0], mz, m, mz, ia, gz * gz, SZ[(i + 1) & 1], rz);
            FN(bg_add)(bg, kz[1], mz, m, mz, ib, gz * gz, TZ[(i + 1) & 1], rz);
        }
        FN(pipeline)(pz + 1, mz, rz, SZ[i & 1], TZ[i & 1], MZ[i & 1], below, NULL, w, bg);
        FN(bg_drain)(bg);
    }
    for (int b = 0; b < gz * gz; b++) oc[b] = ZBLK(MX, r - 1, b);
    FN(pass)(kz[2], mz, mz, m, (const T *const *)MZ[(r - 1) & 1], oc);
#undef ZBLK
    if (sp) sp->tG += now() - t0;
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
    if (PPI(plan[0]) && !lv_leaf(PLV(plan[1])) && PPI(plan[1]) && !lv_leaf(PLV(plan[2])) && PLV(plan[3]) == LV_G &&
        PST(plan[3]) > 0) {
        FN(pipeline2)(plan + 1, m, r, S, Tt, M, deeper, sp);
    } else if (PPI(plan[0]) && !lv_leaf(PLV(plan[1])) && PLV(plan[2]) == LV_G && PST(plan[2]) > 0) {
        FN(pipeline)(plan + 1, m, r, S, Tt, M, deeper, sp, PPW(plan[0]) ? PPW(plan[0]) : fmm_pass_threads(), NULL);
    } else if (PLV(plan[1]) == LV_G && PNE(plan[1]) > 0) {
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

/* C = A B at size n through a plan at the padded size N >= n (fmm.c, padding): A and B copied
 * into zeroed N x N matrices, the result's top-left n x n copied to C; work holds 3 N^2 elements
 * and then plan_work(plan, N) */
static void FN(exec_padded)(const int *plan, size_t n, size_t N, const T *A, size_t lda, const T *B, size_t ldb,
                            T *C, size_t ldc, T *work, FN(split_t) *sp) {
    if (N == n) {
        FN(exec)(plan, n, A, lda, B, ldb, C, ldc, work, sp);
        return;
    }
    T *Ap = work, *Bp = work + N * N, *Cp = work + 2 * N * N, *rest = work + 3 * N * N;
    size_t chunks = 64, step = (N + chunks - 1) / chunks;
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
        for (size_t i = ch * step; i < (ch + 1) * step && i < N; i++) {
            T *ra = Ap + i * N, *rb = Bp + i * N;
            if (i < n) {
                memcpy(ra, A + i * lda, n * sizeof(T));
                memset(ra + n, 0, (N - n) * sizeof(T));
                memcpy(rb, B + i * ldb, n * sizeof(T));
                memset(rb + n, 0, (N - n) * sizeof(T));
            } else {
                memset(ra, 0, N * sizeof(T));
                memset(rb, 0, N * sizeof(T));
            }
        }
    });
    FN(exec)(plan, N, Ap, N, Bp, N, Cp, N, rest, sp);
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
        for (size_t i = ch * step; i < (ch + 1) * step && i < n; i++) memcpy(C + i * ldc, Cp + i * N, n * sizeof(T));
    });
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

/* a pipeline of q sub-problems, each a level ly with blocks my over k GEMM streams with p pass
 * threads, on synthetic inputs (every sub-problem reads A, B and writes C as my * g x my * g
 * matrices), caches evicted before each run: the medians of the times for q = 2 and q = 10 give
 * the steady time per sub-problem (their slope) and the fill and drain (with q = 2 and 4 the
 * slope's noise was a few percent, as large as the differences between configurations, and a
 * plan of 48 sub-problems multiplies it: 16384 f32 predicted 1.580 s, ran 1.718 s) */
#define PIPE_Q1 2
#define PIPE_Q2 10
static void FN(time_pipe)(int ly, size_t my, int k, int p, const T *A, const T *B, T *C, T *work, double *steady,
                          double *over) {
    int py[2] = {ly, LV_G | (k << 8)};
    size_t mx = my * lv_grid(ly);
    T *SX[PIPE_Q2], *TX[PIPE_Q2], *MX[PIPE_Q2];
    for (int q = 0; q < PIPE_Q2; q++) {
        SX[q] = (T *)A;
        TX[q] = (T *)B;
        MX[q] = C;
    }
    double t1[5], t2[5], tot = 0;
    int cnt = 0;
    while (cnt < 5 && tot < 2.0 && !(cnt >= 3 && tot >= 0.3)) {
        evict();
        double t = now();
        FN(pipeline)(py, mx, PIPE_Q1, SX, TX, MX, work, NULL, p, NULL);
        t1[cnt] = now() - t;
        evict();
        t = now();
        FN(pipeline)(py, mx, PIPE_Q2, SX, TX, MX, work, NULL, p, NULL);
        t2[cnt] = now() - t;
        tot += t1[cnt] + t2[cnt];
        cnt++;
    }
    for (int a = 0; a < cnt; a++)
        for (int b = a + 1; b < cnt; b++) {
            if (t1[b] < t1[a]) { double x = t1[a]; t1[a] = t1[b]; t1[b] = x; }
            if (t2[b] < t2[a]) { double x = t2[a]; t2[a] = t2[b]; t2[b] = x; }
        }
    double a1 = t1[(cnt - 1) / 2], a2 = t2[(cnt - 1) / 2], slope = (a2 - a1) / (PIPE_Q2 - PIPE_Q1);
    *steady = slope > 0 ? slope : a2 / PIPE_Q2;
    *over = a1 - PIPE_Q1 * *steady > 0 ? a1 - PIPE_Q1 * *steady : 0;
}

/* the error model's measurements: SW/G, D48/G and D48/D48/G at N_E on uniform random inputs,
 * each against the classical GEMM */
static void FN(calib_errors)(calib_t *c) {
    size_t n = N_E, nn = n * n;
    T *A = alloc_t(nn * sizeof(T)), *B = alloc_t(nn * sizeof(T)), *C = alloc_t(nn * sizeof(T)),
      *R = alloc_t(nn * sizeof(T));
    uint64_t s = 0x2545f4914f6cdd1dull;
    for (size_t i = 0; i < nn; i++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        A[i] = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        B[i] = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
    }
    FN(gemm)(n, A, n, B, n, R, n);
    double rmax = 0;
    for (size_t i = 0; i < nn; i++) rmax = fmax(rmax, fabs((double)R[i]));
    static const char *NAMES[3] = {"sw1", "dps48", "dps48x2"};
    int plans[3][PLAN_MAX];
    size_t wmax = 16;
    for (int i = 0; i < 3; i++) {
        parse_plan(NAMES[i], n, plans[i]);
        size_t w = plan_work(plans[i], n);
        if (w > wmax) wmax = w;
    }
    T *work = alloc_t(wmax * sizeof(T));
    memset(work, 0, wmax * sizeof(T));
    for (int i = 0; i < 3; i++) {
        FN(exec)(plans[i], n, A, n, B, n, C, n, work, NULL);
        double e = 0;
        for (size_t j = 0; j < nn; j++) e = fmax(e, fabs((double)C[j] - (double)R[j]));
        calib_put(c, K_ERR + i, N_E, e / rmax);
        printf("#   %-7s m=%-6d %.3e (error of %s against the classical GEMM)\n", kind_name(K_ERR + i), N_E,
               e / rmax, NAMES[i]);
    }
    free(work);
    free(A); free(B); free(C); free(R);
}

/* measure the entries plan_best needs for n that the cache lacks, and save the cache; A, B, C
 * hold n*n elements, smaller problems use their first m*m as contiguous m x m matrices */
static int FN(calibrate)(calib_t *c, size_t n, const T *A, const T *B, T *C) {
    calib_t need;
    memset(&need, 0, sizeof need);
    calib_need(&need, n);
    size_t wmax = 0;
    int missing = 0, todo[CALIB_MAX];
    for (int i = 0; i < need.n; i++) {
        int kind = need.kind[i];
        size_t m = need.m[i];
        todo[i] = 0;
        if (kind >= K_ERR) {                /* the error model: measured together */
            todo[i] = calib_get(c, kind, m) < 0;
            missing += todo[i];
            continue;
        }
        if (kind >= K_PIPE) {               /* a pipeline: measured with its steady entry */
            int x = kind - K_PIPE, ly = x % 8;
            if ((x / 8) % 2) continue;
            todo[i] = calib_get(c, kind, m) < 0 || calib_get(c, kind + 8, m) < 0;
            if (!todo[i]) continue;
            missing++;
            int plan[2] = {ly, LV_G};
            size_t w = 2 * plan_work(plan, m * lv_grid(ly));
            if (w > wmax) wmax = w;
            continue;
        }
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
    if (!missing) return 0;
    printf("# calibrating %d entries (%s)\n", missing, sizeof(T) == 4 ? "f32" : "f64");
    T *work = alloc_t((wmax + 16) * sizeof(T));
    memset(work, 0, (wmax + 16) * sizeof(T));
    int errors_done = 0;
    for (int i = 0; i < need.n; i++) {
        int kind = need.kind[i];
        size_t m = need.m[i];
        if (!todo[i]) continue;
        if (kind >= K_ERR) {
            if (!errors_done++) FN(calib_errors)(c);
            continue;
        }
        if (kind >= K_PIPE) {
            int x = kind - K_PIPE, ly = x % 8, sp = x / 16;
            double st, ov;
            FN(time_pipe)(ly, m, sp / 16, sp % 16, A, B, C, work, &st, &ov);
            calib_put(c, kind, m, st);
            calib_put(c, kind + 8, m, ov);
            printf("#   %-10s m=%-6zu %.6f s   fill+drain %.6f s\n", kind_name(kind), m, st, ov);
        } else if (lv_leaf(kind)) {
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
    return missing;
}

/* ---- the entry points (fmm.h), this precision ------------------------------------------- */
static int FN(api_gemm)(size_t n, const T *A, size_t lda, const T *B, size_t ldb, T *C, size_t ldc, double gmax) {
    int plan[PLAN_MAX];
    size_t N;
    pthread_mutex_lock(&api_lock);
    api_plan(n, sizeof(T) == 8, gmax, plan, &N, NULL);
    size_t bytes = ((N != n ? 3 * N * N : 0) + plan_work(plan, N)) * sizeof(T);
    if (bytes > api_ws_bytes) {
        free(api_ws);
        api_ws = NULL;
        api_ws_bytes = 0;
        if (posix_memalign(&api_ws, 16384, bytes) != 0) {
            api_ws = NULL;
            pthread_mutex_unlock(&api_lock);
            return -1;
        }
        api_ws_bytes = bytes;
    }
    FN(exec_padded)(plan, n, N, A, lda, B, ldb, C, ldc, (T *)api_ws, NULL);
    pthread_mutex_unlock(&api_lock);
    return 0;
}

static int FN(api_calibrate)(size_t n) {
    size_t nn = n * n;
    T *A = alloc_t(nn * sizeof(T)), *B = alloc_t(nn * sizeof(T)), *C = alloc_t(nn * sizeof(T));
    for (size_t i = 0; i < nn; i++) { A[i] = (T)1 / (T)(1 + i % 7); B[i] = (T)1 / (T)(1 + i % 5); C[i] = 0; }
    pthread_mutex_lock(&api_lock);
    calib_t *c = api_calib(sizeof(T) == 8);
    int cnt = c ? FN(calibrate)(c, n, A, B, C) : 0;
    api_nplans = 0;                         /* the plans may change */
    pthread_mutex_unlock(&api_lock);
    free(A); free(B); free(C);
    return cnt;
}

#undef FN
#undef CAT
#undef CAT_
