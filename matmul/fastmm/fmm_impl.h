/* fmm_impl.h: one precision of the fast matrix multiplication library (fmm.c): the plan
 * executor (fused passes, GEMM streams, pipelines), the calibration and the entry points;
 * included by fmm.c with T (float or double), SUF (f or d), GEMM (cblas_sgemm or cblas_dgemm)
 * and NEON_GEMM_ROWS.  Matrices are row-major; a problem has a shape (m x k)(k x n) and a level
 * of grid g1 x g2 x g3 splits A into g1 x g2 blocks of m/g1 x k/g2, B into g2 x g3 blocks of
 * k/g2 x n/g3 and C into g1 x g3 blocks of m/g1 x n/g3; block (i, j) of X starts at
 * X + i * rows * ld + j * cols with leading dimension ld. */

#define CAT_(a, b) a##b
#define CAT(a, b) CAT_(a, b)
#define FN(name) CAT(name, SUF)

/* a fused kernel: rows r0..r1 of blocks of `cols` columns (kernels.h) */
typedef void (*FN(kern_t))(size_t, size_t, size_t, const T *const *, T *const *, size_t, size_t);

static void FN(gemm)(shape_t s, const T *A, size_t lda, const T *B, size_t ldb, T *C, size_t ldc) {
    GEMM(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)s.m, (int)s.n, (int)s.k, (T)1, A, (int)lda, B,
         (int)ldb, (T)0, C, (int)ldc);
}

/* classical multiplication as g^3 block GEMMs accumulating into C: the fair classical baseline
 * when the library runs faster on blocks than on one big call */
static void FN(classical_blocked)(int g, shape_t s, const T *A, size_t lda, const T *B, size_t ldb, T *C,
                                  size_t ldc) {
    size_t mb = s.m / g, kb = s.k / g, nb = s.n / g;
    for (int i = 0; i < g; i++)
        for (int j = 0; j < g; j++)
            for (int k = 0; k < g; k++)
                GEMM(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)mb, (int)nb, (int)kb, (T)1,
                     A + (size_t)i * mb * lda + (size_t)k * kb, (int)lda, B + (size_t)k * kb * ldb + (size_t)j * nb,
                     (int)ldb, k ? (T)1 : (T)0, C + (size_t)i * mb * ldc + (size_t)j * nb, (int)ldc);
}

/* a fused pass over blocks of rows x cols, the rows split over the cores */
static void FN(pass)(FN(kern_t) k, size_t rows, size_t cols, size_t ld_in, size_t ld_out, const T *const *in,
                     T *const *out) {
    size_t chunks = 64, step = (rows + chunks - 1) / chunks;
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
        size_t r0 = ch * step, r1 = r0 + step < rows ? r0 + step : rows;
        if (r0 < r1) k(cols, ld_in, ld_out, in, out, r0, r1);
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
    else if (lv == LV_R336 && fmm_f64pass()) { k[0] = r336_L_fd; k[1] = r336_R_fd; k[2] = r336_P_fd; }
    else if (lv == LV_R363 && fmm_f64pass()) { k[0] = r363_L_fd; k[1] = r363_R_fd; k[2] = r363_P_fd; }
    else if (lv == LV_R633 && fmm_f64pass()) { k[0] = r633_L_fd; k[1] = r633_R_fd; k[2] = r633_P_fd; }
#endif
    else if (lv == LV_D48) { k[0] = FN(dps48_L_); k[1] = FN(dps48_R_); k[2] = FN(dps48_P_); }
    else if (lv == LV_R336) { k[0] = FN(r336_L_); k[1] = FN(r336_R_); k[2] = FN(r336_P_); }
    else if (lv == LV_R363) { k[0] = FN(r363_L_); k[1] = FN(r363_R_); k[2] = FN(r363_P_); }
    else if (lv == LV_R633) { k[0] = FN(r633_L_); k[1] = FN(r633_R_); k[2] = FN(r633_P_); }
    else { k[0] = FN(sw2_L_); k[1] = FN(sw2_R_); k[2] = FN(sw2_P_); }
}

/* the r products of a level, of shape t, as k single-threaded GEMM streams taking products in
 * turn */
static void FN(gemm_streams)(int r, shape_t t, T *const *S, T *const *Tt, T *const *M, int k) {
    atomic_int next = 0;
    atomic_int *pn = &next;
    dispatch_apply((size_t)k, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t w) {
        (void)w;
        enum BLAS_THREADING old = BLASGetThreading();
        BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
        for (int q; (q = atomic_fetch_add(pn, 1)) < r;) FN(gemm)(t, S[q], t.k, Tt[q], t.n, M[q], t.n);
        BLASSetThreading(old);
    });
}

/* the r square products of size m of a level: the first r - j as k single-threaded GEMM streams
 * taking products in turn, the last j by w NEON threads, all at once.  A NEON task is a slab of
 * FMM_NEON_SLAB rows of a product (default 0: the whole product; each task packs all of B
 * again, so small slabs multiply the traffic through the L2 the SME units share).  The packing
 * buffers are allocated once, for the largest m seen. */
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
    shape_t sm = sq(m);
    dispatch_apply((size_t)(k + w), dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t id) {
        if ((int)id < k) {
            enum BLAS_THREADING old = BLASGetThreading();
            BLASSetThreading(BLAS_THREADING_SINGLE_THREADED);
            for (int q; (q = atomic_fetch_add(pn, 1)) < r - j;) FN(gemm)(sm, S[q], m, Tt[q], m, M[q], m);
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
    T *S[2][64], *Tt[2][64], *M[2][64];
} FN(pipe_t);

/* background passes: up to three passes in row chunks, which the pass threads of a pipeline run
 * when their own passes are done while the GEMMs of the step still run; the rest is drained
 * after the pipeline */
typedef struct {
    int n, nch;
    FN(kern_t) k[3];
    size_t rows[3], cols[3], ldi[3], ldo[3];
    const T *in[3][64];
    T *out[3][64];
    atomic_int next;
} FN(bg_t);

static void FN(bg_add)(FN(bg_t) *bg, FN(kern_t) k, size_t rows, size_t cols, size_t ldi, size_t ldo,
                       const T *const *in, int nin, T *const *out, int nout) {
    int p = bg->n++;
    bg->k[p] = k;
    bg->rows[p] = rows;
    bg->cols[p] = cols;
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
    size_t step = (bg->rows[p] + bg->nch - 1) / bg->nch, r0 = (size_t)c * step,
           r1 = r0 + step < bg->rows[p] ? r0 + step : bg->rows[p];
    if (r0 < r1) bg->k[p](bg->cols[p], bg->ldi[p], bg->ldo[p], bg->in[p], bg->out[p], r0, r1);
    return 1;
}

static void FN(bg_drain)(FN(bg_t) *bg) {
    dispatch_apply(16, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t i) {
        (void)i;
        while (FN(bg_chunk)(bg)) {}
    });
}

/* the r sub-problems of shape t (the products of the level above: SX[q] (t.m x t.k, ld t.k) times
 * TX[q] (t.k x t.n, ld t.n) into MX[q] (t.m x t.n, ld t.n)), each a level Y over k GEMM streams */
static void FN(pipeline)(const int *py, shape_t t, int r, T *const *SX, T *const *TX, T *const *MX, T *work,
                         FN(split_t) *sp, int w, FN(bg_t) *bg) {
    int ly = PLV(py[0]), ry = lv_rank(ly), k = PST(py[1]);
    int gy1 = LVDEF[ly].g1, gy2 = LVDEF[ly].g2, gy3 = LVDEF[ly].g3;
    shape_t ty = lv_sub(ly, t);
    size_t pad = fmm_pad(), bsS = ty.m * ty.k + pad, bsT = ty.k * ty.n + pad, bsM = ty.m * ty.n + pad,
           set = (size_t)ry * (bsS + bsT + bsM);
    FN(kern_t) ky[3];
    FN(kernels)(ly, ky);
    FN(kern_t) kL = ky[0], kR = ky[1], kP = ky[2];  /* blocks cannot capture arrays */
    FN(pipe_t) pp;
    FN(pipe_t) *P = &pp;
    for (int b = 0; b < 2; b++)
        for (int j = 0; j < ry; j++) {
            P->S[b][j] = work + b * set + (size_t)j * bsS;
            P->Tt[b][j] = work + b * set + (size_t)ry * bsS + (size_t)j * bsT;
            P->M[b][j] = work + b * set + (size_t)ry * (bsS + bsT) + (size_t)j * bsM;
        }
    int nch = 16;                               /* row chunks per pass */
    size_t rows_lp = ty.m, rows_r = ty.k;       /* block rows of the L and P passes, of the R pass */
    double t0 = now();
    for (int q = -1; q <= r; q++) {
        int qo = q - 1, qi = q + 1, gq = q >= 0 && q < r;
        int have_out = qo >= 0, have_in = qi < r;
        /* block pointers of sub-problem qi's inputs (blocks of SX[qi], TX[qi]) and qo's output */
        T *in_s[64], *in_t[64], *out_c[64];
        if (have_in) {
            for (int b = 0; b < gy1 * gy2; b++) in_s[b] = SX[qi] + (size_t)(b / gy2) * ty.m * t.k + (size_t)(b % gy2) * ty.k;
            for (int b = 0; b < gy2 * gy3; b++) in_t[b] = TX[qi] + (size_t)(b / gy3) * ty.k * t.n + (size_t)(b % gy3) * ty.n;
        }
        if (have_out)
            for (int b = 0; b < gy1 * gy3; b++) out_c[b] = MX[qo] + (size_t)(b / gy3) * ty.m * t.n + (size_t)(b % gy3) * ty.n;
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
                    FN(gemm)(ty, P->S[sg][j], ty.k, P->Tt[sg][j], ty.n, P->M[sg][j], ty.n);
                BLASSetThreading(old);
                atomic_fetch_sub(pga, 1);
            } else {
                for (int tk; (tk = atomic_fetch_add(pnp, 1)) < ntask;) {
                    int pass = have_out ? (tk < nch ? 2 : (tk < 2 * nch ? 0 : 1)) : (tk < nch ? 0 : 1);
                    size_t rows = pass == 1 ? rows_r : rows_lp, step = (rows + nch - 1) / nch;
                    size_t c = (size_t)(tk % nch), r0 = c * step, r1 = r0 + step < rows ? r0 + step : rows;
                    if (r0 >= r1) continue;
                    if (pass == 0) kL(ty.k, t.k, ty.k, ins, P->S[si], r0, r1);
                    else if (pass == 1) kR(ty.n, t.n, ty.n, int_, P->Tt[si], r0, r1);
                    else kP(ty.n, ty.n, t.n, (const T *const *)P->M[so], outc, r0, r1);
                }
                if (bg)                                 /* the level above's passes, while GEMMs run */
                    while (atomic_load(pga) > 0 && FN(bg_chunk)(bg)) {}
            }
        });
    }
    if (sp) sp->tG += now() - t0;   /* the pipeline: GEMMs with the passes below hidden in them */
}

/* the r sub-problems of shape t, each a pipelined level Z (pz[0]) over Y (pz[1]) and GEMM streams
 * (pz[2]): Z's own passes run in the background of the neighbouring products' pipelines.  While
 * product i's pipeline runs, its pass threads, when free, write product i - 1's result (Z's P
 * pass) and the factors of product i + 1 (Z's L and R passes); what is left runs on all cores
 * before product i + 1.  Z's scratch is double-buffered (sets i % 2), the pipelines' shared. */
static void FN(pipeline2)(const int *pz, shape_t t, int r, T *const *SX, T *const *TX, T *const *MX, T *work,
                          FN(split_t) *sp) {
    int lz = PLV(pz[0]), rz = lv_rank(lz), gz1 = LVDEF[lz].g1, gz2 = LVDEF[lz].g2, gz3 = LVDEF[lz].g3;
    int w = PPW(pz[0]) ? PPW(pz[0]) : fmm_pass_threads();
    shape_t tz = lv_sub(lz, t);
    size_t pad = fmm_pad(), bsS = tz.m * tz.k + pad, bsT = tz.k * tz.n + pad, bsM = tz.m * tz.n + pad,
           set = (size_t)rz * (bsS + bsT + bsM);
    FN(kern_t) kz[3];
    FN(kernels)(lz, kz);
    T *SZ[2][64], *TZ[2][64], *MZ[2][64];
    for (int b = 0; b < 2; b++)
        for (int j = 0; j < rz; j++) {
            SZ[b][j] = work + b * set + (size_t)j * bsS;
            TZ[b][j] = work + b * set + (size_t)rz * bsS + (size_t)j * bsT;
            MZ[b][j] = work + b * set + (size_t)rz * (bsS + bsT) + (size_t)j * bsM;
        }
    T *below = work + 2 * set;
#define ABLK(q, b) (SX[q] + (size_t)((b) / gz2) * tz.m * t.k + (size_t)((b) % gz2) * tz.k)
#define BBLK(q, b) (TX[q] + (size_t)((b) / gz3) * tz.k * t.n + (size_t)((b) % gz3) * tz.n)
#define CBLK(q, b) (MX[q] + (size_t)((b) / gz3) * tz.m * t.n + (size_t)((b) % gz3) * tz.n)
    double t0 = now();
    const T *ia[64], *ib[64];
    T *oc[64];
    for (int b = 0; b < gz1 * gz2; b++) ia[b] = ABLK(0, b);
    for (int b = 0; b < gz2 * gz3; b++) ib[b] = BBLK(0, b);
    FN(pass)(kz[0], tz.m, tz.k, t.k, tz.k, ia, SZ[0]);
    FN(pass)(kz[1], tz.k, tz.n, t.n, tz.n, ib, TZ[0]);
    for (int i = 0; i < r; i++) {
        FN(bg_t) bgv;
        FN(bg_t) *bg = &bgv;
        bg->n = 0;
        bg->nch = 64;
        atomic_init(&bg->next, 0);
        if (i >= 1) {
            for (int b = 0; b < gz1 * gz3; b++) oc[b] = CBLK(i - 1, b);
            FN(bg_add)(bg, kz[2], tz.m, tz.n, tz.n, t.n, (const T *const *)MZ[(i - 1) & 1], rz, oc, gz1 * gz3);
        }
        if (i + 1 < r) {
            for (int b = 0; b < gz1 * gz2; b++) ia[b] = ABLK(i + 1, b);
            for (int b = 0; b < gz2 * gz3; b++) ib[b] = BBLK(i + 1, b);
            FN(bg_add)(bg, kz[0], tz.m, tz.k, t.k, tz.k, ia, gz1 * gz2, SZ[(i + 1) & 1], rz);
            FN(bg_add)(bg, kz[1], tz.k, tz.n, t.n, tz.n, ib, gz2 * gz3, TZ[(i + 1) & 1], rz);
        }
        FN(pipeline)(pz + 1, tz, rz, SZ[i & 1], TZ[i & 1], MZ[i & 1], below, NULL, w, bg);
        FN(bg_drain)(bg);
    }
    for (int b = 0; b < gz1 * gz3; b++) oc[b] = CBLK(r - 1, b);
    FN(pass)(kz[2], tz.m, tz.n, tz.n, t.n, (const T *const *)MZ[(r - 1) & 1], oc);
#undef ABLK
#undef BBLK
#undef CBLK
    if (sp) sp->tG += now() - t0;
}

/* C = A B on a problem of shape s by a plan (plan[0] the top level); work holds plan_work(plan, s)
 * elements.  A fused level splits A, B, C into its grid of blocks, writes the r factors S_q and
 * T_q (one pass per side), computes M_q = S_q T_q by the rest of the plan (the scratch below this
 * level reused product after product) and writes C from the M_q (one pass).  GEMM time is counted
 * where the GEMMs run, pass time at every level. */
static void FN(exec)(const int *plan, shape_t s, const T *A, size_t lda, const T *B, size_t ldb, T *C,
                     size_t ldc, T *work, FN(split_t) *sp) {
    int lv = PLV(plan[0]);
    if (lv == LV_NONE) return;
    if (lv_leaf(lv)) {
        double t = now();
        if (lv == LV_G) FN(gemm)(s, A, lda, B, ldb, C, ldc);
        else FN(classical_blocked)(lv_grid(lv), s, A, lda, B, ldb, C, ldc);
        if (sp) sp->tG += now() - t;
        return;
    }
    int g1 = LVDEF[lv].g1, g2 = LVDEF[lv].g2, g3 = LVDEF[lv].g3, r = lv_rank(lv);
    FN(kern_t) k[3];
    FN(kernels)(lv, k);
    shape_t t = lv_sub(lv, s);
    const T *Ab[64], *Bb[64];
    T *Cb[64], *S[64], *Tt[64], *M[64];
    for (int q = 0; q < g1 * g2; q++) Ab[q] = A + (size_t)(q / g2) * t.m * lda + (size_t)(q % g2) * t.k;
    for (int q = 0; q < g2 * g3; q++) Bb[q] = B + (size_t)(q / g3) * t.k * ldb + (size_t)(q % g3) * t.n;
    for (int q = 0; q < g1 * g3; q++) Cb[q] = C + (size_t)(q / g3) * t.m * ldc + (size_t)(q % g3) * t.n;
    /* scratch blocks pad apart: with pad 0 every block starts at the same offset modulo any power
     * of two up to its size, so element c of every stream maps to one cache set */
    size_t pad = fmm_pad(), bsS = t.m * t.k + pad, bsT = t.k * t.n + pad, bsM = t.m * t.n + pad;
    for (int q = 0; q < r; q++) {
        S[q] = work + (size_t)q * bsS;
        Tt[q] = work + (size_t)r * bsS + (size_t)q * bsT;
        M[q] = work + (size_t)r * (bsS + bsT) + (size_t)q * bsM;
    }
    T *deeper = work + (size_t)r * (bsS + bsT + bsM);
    double t0 = now();
    FN(pass)(k[0], t.m, t.k, lda, t.k, Ab, S);
    double t1 = now();
    FN(pass)(k[1], t.k, t.n, ldb, t.n, Bb, Tt);
    double t2 = now();
    if (sp) {
        sp->tL += t1 - t0;
        sp->tR += t2 - t1;
    }
    if (PPI(plan[0]) && !lv_leaf(PLV(plan[1])) && PPI(plan[1]) && !lv_leaf(PLV(plan[2])) && PLV(plan[3]) == LV_G &&
        PST(plan[3]) > 0) {
        FN(pipeline2)(plan + 1, t, r, S, Tt, M, deeper, sp);
    } else if (PPI(plan[0]) && !lv_leaf(PLV(plan[1])) && PLV(plan[2]) == LV_G && PST(plan[2]) > 0) {
        FN(pipeline)(plan + 1, t, r, S, Tt, M, deeper, sp, PPW(plan[0]) ? PPW(plan[0]) : fmm_pass_threads(), NULL);
    } else if (PLV(plan[1]) == LV_G && PNE(plan[1]) > 0 && shape_sq(t)) {
        double tt = now();
        FN(gemm_hybrid)(r, t.m, S, Tt, M, PST(plan[1]), PNE(plan[1]), fmm_neon_threads());
        if (sp) sp->tG += now() - tt;
    } else if (PLV(plan[1]) == LV_G && PST(plan[1]) > 0) {
        double tt = now();
        FN(gemm_streams)(r, t, S, Tt, M, PST(plan[1]));
        if (sp) sp->tG += now() - tt;
    } else {
        for (int q = 0; q < r; q++) FN(exec)(plan + 1, t, S[q], t.k, Tt[q], t.n, M[q], t.n, deeper, sp);
    }
    double t3 = now();
    FN(pass)(k[2], t.m, t.n, t.n, ldc, (const T *const *)M, Cb);
    if (sp) sp->tP += now() - t3;
}

/* C = A B at size n through a plan at the padded size N >= n (fmm.c, padding): A and B copied
 * into zeroed N x N matrices, the result's top-left n x n copied to C; work holds 3 N^2 elements
 * and then plan_work(plan, N) */
static void FN(exec_padded)(const int *plan, size_t n, size_t N, const T *A, size_t lda, const T *B, size_t ldb,
                            T *C, size_t ldc, T *work, FN(split_t) *sp) {
    if (N == n) {
        FN(exec)(plan, sq(n), A, lda, B, ldb, C, ldc, work, sp);
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
    FN(exec)(plan, sq(N), Ap, N, Bp, N, Cp, N, rest, sp);
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
        for (size_t i = ch * step; i < (ch + 1) * step && i < n; i++) memcpy(C + i * ldc, Cp + i * N, n * sizeof(T));
    });
}

/* calibration timing of a plan on a problem of shape s (A, B, C contiguous, s.m*s.k, s.k*s.n and
 * s.m*s.n elements): caches evicted before each run; repeated until 3 runs and 0.3 s, or 2 s, or
 * 15 runs; the median (the lower middle for an even count) */
static double FN(time_plan)(const int *plan, shape_t s, const T *A, const T *B, T *C, T *work) {
    double ts[15], tot = 0;
    int cnt = 0;
    while (cnt < 15 && tot < 2.0 && !(cnt >= 3 && tot >= 0.3)) {
        evict();
        double t = now();
        FN(exec)(plan, s, A, s.k, B, s.n, C, s.n, work, NULL);
        ts[cnt] = now() - t;
        tot += ts[cnt++];
    }
    for (int a = 0; a < cnt; a++)
        for (int b = a + 1; b < cnt; b++)
            if (ts[b] < ts[a]) { double x = ts[a]; ts[a] = ts[b]; ts[b] = x; }
    return ts[(cnt - 1) / 2];
}

/* one fused level of type lv whose products have shape t, with GEMM products (as `streams`
 * streams), caches evicted before each run, repeated as in time_plan: the medians of its pass
 * time and of its GEMM time per product */
static void FN(time_level)(int lv, shape_t t, int streams, const T *A, const T *B, T *C, T *work,
                           double *passes, double *gemm) {
    int plan[2] = {lv, LV_G | (streams << 8)};
    shape_t s = lv_up(lv, t);
    double tp[15], tg[15], tot = 0;
    int cnt = 0;
    while (cnt < 15 && tot < 2.0 && !(cnt >= 3 && tot >= 0.3)) {
        FN(split_t) sp = {0};
        evict();
        double t0 = now();
        FN(exec)(plan, s, A, s.k, B, s.n, C, s.n, work, &sp);
        tot += now() - t0;
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

/* a pipeline of q sub-problems, each a level ly whose products have shape ty over k GEMM streams
 * with p pass threads, on synthetic inputs (every sub-problem reads A, B and writes C as the
 * level's problem), caches evicted before each run: the medians of the times for q = 2 and q = 10
 * give the steady time per sub-problem (their slope) and the fill and drain (with q = 2 and 4 the
 * slope's noise was a few percent, as large as the differences between configurations, and a
 * plan of 48 sub-problems multiplies it: 16384 f32 predicted 1.580 s, ran 1.718 s) */
#define PIPE_Q1 2
#define PIPE_Q2 10
static void FN(time_pipe)(int ly, shape_t ty, int k, int p, const T *A, const T *B, T *C, T *work, double *steady,
                          double *over) {
    int py[2] = {ly, LV_G | (k << 8)};
    shape_t t = lv_up(ly, ty);
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
        double t0 = now();
        FN(pipeline)(py, t, PIPE_Q1, SX, TX, MX, work, NULL, p, NULL);
        t1[cnt] = now() - t0;
        evict();
        t0 = now();
        FN(pipeline)(py, t, PIPE_Q2, SX, TX, MX, work, NULL, p, NULL);
        t2[cnt] = now() - t0;
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

/* the error model's measurements: the ERR_PLANS at N_E on uniform random inputs, each against
 * the classical GEMM */
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
    FN(gemm)(sq(n), A, n, B, n, R, n);
    double rmax = 0;
    for (size_t i = 0; i < nn; i++) rmax = fmax(rmax, fabs((double)R[i]));
    int plans[NERR][PLAN_MAX];
    size_t wmax = 16;
    for (int i = 0; i < NERR; i++) {
        if (!parse_plan(ERR_PLANS[i], sq(n), plans[i])) {
            fprintf(stderr, "calib_errors: plan %s does not parse at %zu\n", ERR_PLANS[i], n);
            exit(1);
        }
        size_t w = plan_work(plans[i], sq(n));
        if (w > wmax) wmax = w;
    }
    T *work = alloc_t(wmax * sizeof(T));
    memset(work, 0, wmax * sizeof(T));
    for (int i = 0; i < NERR; i++) {
        FN(exec)(plans[i], sq(n), A, n, B, n, C, n, work, NULL);
        double e = 0;
        for (size_t j = 0; j < nn; j++) e = fmax(e, fabs((double)C[j] - (double)R[j]));
        calib_put(c, K_ERR + i, sq(N_E), e / rmax);
        printf("#   %-7s m=%-6d %.3e (error of %s against the classical GEMM)\n", kind_name(K_ERR + i), N_E,
               e / rmax, ERR_PLANS[i]);
    }
    free(work);
    free(A); free(B); free(C); free(R);
}

/* measure the entries plan_best needs for n that the cache lacks, and save the cache; A, B, C
 * hold n*n elements, smaller problems use their first elements as contiguous matrices */
static int FN(calibrate)(calib_t *c, size_t n, const T *A, const T *B, T *C) {
    calib_t need;
    memset(&need, 0, sizeof need);
    calib_need(&need, sq(n));
    size_t wmax = 0;
    int missing = 0, todo[CALIB_MAX];
    for (int i = 0; i < need.n; i++) {
        int kind = need.kind[i];
        shape_t s = need.s[i];
        todo[i] = 0;
        if (kind >= K_ERR) {                /* the error model: measured together */
            todo[i] = calib_get(c, kind, s) < 0;
            missing += todo[i];
            continue;
        }
        if (kind >= K_PIPE) {               /* a pipeline: measured with its steady entry */
            int x = kind - K_PIPE, ly = x % 16;
            if ((x / 16) % 2) continue;
            todo[i] = calib_get(c, kind, s) < 0 || calib_get(c, kind + 16, s) < 0;
            if (!todo[i]) continue;
            missing++;
            int plan[2] = {ly, LV_G};
            size_t w = 2 * plan_work(plan, lv_up(ly, s));
            if (w > wmax) wmax = w;
            continue;
        }
        if (kind >= K_GIN) continue;
        todo[i] = calib_get(c, kind, s) < 0;
        for (int k = 0; !lv_leaf(kind) && k < NSTREAMS; k++)
            if (calib_get(c, kind_gin(kind, STREAMS[k]), s) < 0) todo[i] = 1;
        if (!todo[i]) continue;
        missing++;
        int plan[2] = {kind, LV_G};
        size_t w = lv_leaf(kind) ? 0 : plan_work(plan, lv_up(kind, s));
        if (w > wmax) wmax = w;
    }
    if (!missing) return 0;
    printf("# calibrating %d entries (%s)\n", missing, sizeof(T) == 4 ? "f32" : "f64");
    T *work = alloc_t((wmax + 16) * sizeof(T));
    memset(work, 0, (wmax + 16) * sizeof(T));
    int errors_done = 0;
    for (int i = 0; i < need.n; i++) {
        int kind = need.kind[i];
        shape_t s = need.s[i];
        if (!todo[i]) continue;
        if (kind >= K_ERR) {
            if (!errors_done++) FN(calib_errors)(c);
            continue;
        }
        if (kind >= K_PIPE) {
            int x = kind - K_PIPE, ly = x % 16, sp = x / 32;
            double st, ov;
            FN(time_pipe)(ly, s, sp / 16, sp % 16, A, B, C, work, &st, &ov);
            calib_put(c, kind, s, st);
            calib_put(c, kind + 16, s, ov);
            printf("#   %-10s m=%zux%zux%zu %.6f s   fill+drain %.6f s\n", kind_name(kind), s.m, s.k, s.n, st, ov);
        } else if (lv_leaf(kind)) {
            int plan[1] = {kind};
            double t = FN(time_plan)(plan, s, A, B, C, work);
            calib_put(c, kind, s, t);
            printf("#   %-4s m=%zux%zux%zu %.6f s\n", kind_name(kind), s.m, s.k, s.n, t);
        } else {
            printf("#   %-4s m=%zux%zux%zu", kind_name(kind), s.m, s.k, s.n);
            for (int k = 0; k < NSTREAMS; k++) {
                double tp, tg;
                FN(time_level)(kind, s, STREAMS[k], A, B, C, work, &tp, &tg);
                if (k == 0) {
                    calib_put(c, kind, s, tp);
                    printf(" %.6f s ", tp);
                }
                calib_put(c, kind_gin(kind, STREAMS[k]), s, tg);
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
    size_t bytes = ((N != n ? 3 * N * N : 0) + plan_work(plan, sq(N))) * sizeof(T);
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
