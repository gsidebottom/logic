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
static void FN(classical_blocked)(int g, size_t n, const T *A, const T *B, T *C) {
    size_t m = n / g;
    for (int i = 0; i < g; i++)
        for (int j = 0; j < g; j++)
            for (int k = 0; k < g; k++)
                GEMM(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)m, (int)m, (int)m, (T)1,
                     A + (size_t)i * m * n + (size_t)k * m, (int)n, B + (size_t)k * m * n + (size_t)j * m,
                     (int)n, k ? (T)1 : (T)0, C + (size_t)i * m * n + (size_t)j * m, (int)n);
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

static void FN(sw_rec)(int depth, size_t n, const T *A, size_t lda, const T *B, size_t ldb, T *C,
                       size_t ldc, T *work, FN(split_t) *sp);
static void FN(fused_level)(FN(kern_t) kL, FN(kern_t) kR, FN(kern_t) kP, int g, int r, size_t n,
                            const T *A, size_t lda, const T *B, size_t ldb, T *C, size_t ldc, T *work,
                            FN(split_t) *sp, sub_t sub);

/* M = S T at size m: a GEMM, one fused Strassen level, or one fused level of our 48-scheme;
 * work is the scratch below this level (reused product after product) */
static void FN(product)(sub_t sub, size_t m, const T *S, const T *Tt, T *M, T *work, FN(split_t) *sp) {
    if (sub == SUB_GEMM) {
        double t = now();
        FN(gemm)(m, S, m, Tt, m, M, m);
        if (sp) sp->tG += now() - t;
    } else if (sub == SUB_SW1) {
        FN(sw_rec)(1, m, S, m, Tt, m, M, m, work, sp);
    } else {
        FN(fused_level)(FN(dps48_L_), FN(dps48_R_), FN(dps48_P_), 4, 48, m, S, m, Tt, m, M, m, work, sp,
                        SUB_GEMM);
    }
}

/* one level of a scheme: grid g, nb = g*g blocks, rank r; work holds 3 r blocks of m*m (S, T,
 * M) followed by the scratch of the sub-method; GEMM time is counted where the GEMMs run, pass
 * time at every level */
static void FN(fused_level)(FN(kern_t) kL, FN(kern_t) kR, FN(kern_t) kP, int g, int r, size_t n,
                            const T *A, size_t lda, const T *B, size_t ldb, T *C, size_t ldc, T *work,
                            FN(split_t) *sp, sub_t sub) {
    size_t m = n / g;
    const T *Ab[16], *Bb[16];
    T *Cb[16], *S[64], *Tt[64], *M[64];
    for (int k = 0; k < g * g; k++) {
        Ab[k] = A + (k / g) * m * lda + (k % g) * m;
        Bb[k] = B + (k / g) * m * ldb + (k % g) * m;
        Cb[k] = C + (k / g) * m * ldc + (k % g) * m;
    }
    /* scratch blocks m*m + pad apart: with pad 0 every block starts at the same offset modulo
     * any power of two up to m*m, so element c of every stream maps to one cache set */
    size_t bs = m * m + fmm_pad();
    for (int k = 0; k < r; k++) {
        S[k] = work + (size_t)k * bs;
        Tt[k] = work + (size_t)(r + k) * bs;
        M[k] = work + (size_t)(2 * r + k) * bs;
    }
    T *deeper = work + (size_t)3 * r * bs;
    double t0 = now();
    FN(pass)(kL, m, lda, m, Ab, S);
    double t1 = now();
    FN(pass)(kR, m, ldb, m, Bb, Tt);
    double t2 = now();
    if (sp) {
        sp->tL += t1 - t0;
        sp->tR += t2 - t1;
    }
    for (int k = 0; k < r; k++) FN(product)(sub, m, S[k], Tt[k], M[k], deeper, sp);
    double t3 = now();
    FN(pass)(kP, m, m, ldc, (const T *const *)M, Cb);
    if (sp) sp->tP += now() - t3;
}

/* Strassen-Winograd, depth levels, each level one fused pass per side; work for level l at
 * offset sum of 21 (n / 2^j)^2 over the levels above */
static void FN(sw_rec)(int depth, size_t n, const T *A, size_t lda, const T *B, size_t ldb, T *C,
                       size_t ldc, T *work, FN(split_t) *sp) {
    if (depth == 0) {
        double t = now();
        FN(gemm)(n, A, lda, B, ldb, C, ldc);
        if (sp) sp->tG += now() - t;
        return;
    }
    size_t m = n / 2;
    const T *Ab[4], *Bb[4];
    T *Cb[4], *S[7], *Tt[7], *M[7];
    for (int k = 0; k < 4; k++) {
        Ab[k] = A + (k / 2) * m * lda + (k % 2) * m;
        Bb[k] = B + (k / 2) * m * ldb + (k % 2) * m;
        Cb[k] = C + (k / 2) * m * ldc + (k % 2) * m;
    }
    size_t bs = m * m + fmm_pad();
    for (int k = 0; k < 7; k++) {
        S[k] = work + (size_t)k * bs;
        Tt[k] = work + (size_t)(7 + k) * bs;
        M[k] = work + (size_t)(14 + k) * bs;
    }
    T *deeper = work + (size_t)21 * bs;
    double t0 = now();
    FN(pass)(FN(sw_L_), m, lda, m, Ab, S);
    FN(pass)(FN(sw_R_), m, ldb, m, Bb, Tt);
    if (sp) sp->tL += now() - t0;
    for (int k = 0; k < 7; k++) FN(sw_rec)(depth - 1, m, S[k], m, Tt[k], m, M[k], m, deeper, sp);
    double t1 = now();
    FN(pass)(FN(sw_P_), m, m, ldc, (const T *const *)M, Cb);
    if (sp) sp->tP += now() - t1;
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

static int FN(run_method)(const char *meth, size_t n, const T *A, const T *B, T *C, T *work, T **temps,
                          FN(split_t) *sp) {
    if (!strcmp(meth, "classical")) {
        double t = now();
        FN(gemm)(n, A, n, B, n, C, n);
        if (sp) sp->tG += now() - t;
    } else if (!strncmp(meth, "blk", 3)) {
        double t = now();
        FN(classical_blocked)(atoi(meth + 3), n, A, B, C);
        if (sp) sp->tG += now() - t;
    } else if (!strcmp(meth, "sw1")) {
        FN(sw_rec)(1, n, A, n, B, n, C, n, work, sp);
    } else if (!strcmp(meth, "sw2rec")) {
        FN(sw_rec)(2, n, A, n, B, n, C, n, work, sp);
    } else if (!strcmp(meth, "sw3rec")) {
        FN(sw_rec)(3, n, A, n, B, n, C, n, work, sp);
    } else if (!strcmp(meth, "sw4rec")) {
        FN(sw_rec)(4, n, A, n, B, n, C, n, work, sp);
    } else if (!strcmp(meth, "sw2")) {
        FN(fused_level)(FN(sw2_L_), FN(sw2_R_), FN(sw2_P_), 4, 49, n, A, n, B, n, C, n, work, sp, SUB_GEMM);
    } else if (!strcmp(meth, "sw2sw")) {
        FN(fused_level)(FN(sw2_L_), FN(sw2_R_), FN(sw2_P_), 4, 49, n, A, n, B, n, C, n, work, sp, SUB_SW1);
    } else if (!strcmp(meth, "dps48")) {
        FN(fused_level)(FN(dps48_L_), FN(dps48_R_), FN(dps48_P_), 4, 48, n, A, n, B, n, C, n, work, sp, SUB_GEMM);
    } else if (!strcmp(meth, "dps48sw")) {
        FN(fused_level)(FN(dps48_L_), FN(dps48_R_), FN(dps48_P_), 4, 48, n, A, n, B, n, C, n, work, sp, SUB_SW1);
    } else if (!strcmp(meth, "dps48x2")) {
        FN(fused_level)(FN(dps48_L_), FN(dps48_R_), FN(dps48_P_), 4, 48, n, A, n, B, n, C, n, work, sp, SUB_DPS48);
    } else if (!strcmp(meth, "dps48ops")) {
        FN(dps48_opbyop)(n, A, B, C, work, temps, sp);
    } else {
        return 0;
    }
    return 1;
}

static void FN(bench)(size_t n, const char *methods, int reps) {
    size_t nn = n * n;
    T *A = alloc_t(nn * sizeof(T)), *B = alloc_t(nn * sizeof(T)), *C = alloc_t(nn * sizeof(T)),
      *Cref = alloc_t(nn * sizeof(T));
    /* workspace: 3 * 49 blocks of (n/4)^2 covers every method (sw recursion: 21 n^2/4 + 21 n^2/16 + ...) */
    size_t wsz = (size_t)3 * 49 * (nn / 16 + fmm_pad()) + (size_t)21 * (nn / 64 + fmm_pad())
                 + (size_t)3 * 48 * (nn / 256 + fmm_pad()) + 1024;
    size_t swz = (size_t)(21.0 * nn / 4 * 1.34) + 64 + 4 * 21 * fmm_pad();
    if (swz > wsz) wsz = swz;
    T *work = alloc_t(wsz * sizeof(T));
    uint64_t s = 0x9e3779b97f4a7c15ull;
    for (size_t i = 0; i < nn; i++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        A[i] = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        B[i] = (T)((double)(s >> 11) / 9007199254740992.0 * 2 - 1);
    }
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
    char buf[512], *names[16];
    int nm = 0;
    strncpy(buf, methods, sizeof buf - 1);
    buf[sizeof buf - 1] = 0;
    for (char *meth = strtok(buf, ","); meth && nm < 16; meth = strtok(NULL, ","))
        if (FN(run_method)(meth, n, A, B, C, work, temps, NULL)) names[nm++] = meth;  /* warm-up */
        else printf("unknown method %s\n", meth);
    double times[16][32];
    FN(split_t) sp[16];
    memset(sp, 0, sizeof sp);
    double err[16] = {0};
    for (int q = 0; q < reps; q++)          /* rounds: drift hits every method alike */
        for (int j = 0; j < nm; j++) {
            double t = now();
            FN(run_method)(names[j], n, A, B, C, work, temps, &sp[j]);
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
        if (!strcmp(names[j], "classical")) tclass = med;
        printf("%-10s n=%-6zu %s  min %8.3f s  med %8.3f s  %7.1f GFLOP/s(2n^3)  speedup %5.3f  "
               "relerr %.2e  split L %.3f R %.3f gemm %.3f P %.3f\n",
               names[j], n, sizeof(T) == 4 ? "f32" : "f64", best, med, 2.0 * n * n * (double)n / med / 1e9,
               tclass > 0 ? tclass / med : 0.0, err[j] / cmax, sp[j].tL / reps, sp[j].tR / reps,
               sp[j].tG / reps, sp[j].tP / reps);
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
