/* gemms_impl.h: a competitor baseline, the conventional Strassen-Winograd product as IBM's ESSL
 * ships it in _GEMMS: Winograd's variant of Strassen's algorithm (15 block additions per level),
 * recursing "up to four times", each step halving the dimensions, over the vendor GEMM (here
 * Accelerate's).  ESSL's own code is closed and does not run on this machine; this is the
 * published algorithm with the usual schedule of two temporaries per level (as in Douglas, Heroux,
 * Slishman and Smith's GEMMW and in Boyer, Dumas, Pernet and Zhou, ISSAC 2009), every block addition a
 * separate parallel pass over memory and every product one multithreaded GEMM call.  At the
 * last level two additions ride in the GEMM's beta (C21 -= A22 T4, C11 = P1 + A12 B21), ESSL's
 * "minor changes for tuning" being unpublished.  Included by bench_impl.h once per precision
 * (T, SUF, GEMM, FN defined there). */

/* Z = X + Y (sub 0) or X - Y (sub 1), or Z = X (sub 2), over an r x c block; Z may be X or Y */
static void FN(gw_op)(int sub, size_t r, size_t c, T *Z, size_t ldz, const T *X, size_t ldx, const T *Y,
                      size_t ldy) {
    size_t chunks = r < 64 ? r : 64, step = (r + chunks - 1) / chunks;
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {
        size_t r0 = ch * step, r1 = r0 + step < r ? r0 + step : r;
        for (size_t i = r0; i < r1; i++) {
            T *z = Z + i * ldz;
            const T *x = X + i * ldx, *y = Y ? Y + i * ldy : NULL;
            if (sub == 0) for (size_t j = 0; j < c; j++) z[j] = x[j] + y[j];
            else if (sub == 1) for (size_t j = 0; j < c; j++) z[j] = x[j] - y[j];
            else memcpy(z, x, c * sizeof(T));
        }
    });
}

/* the workspace (elements) of lv levels on (m x k)(k x n) */
static size_t FN(gemms_work)(int lv, size_t m, size_t k, size_t n) {
    if (lv <= 0 || m % 2 || k % 2 || n % 2) return 0;
    size_t m2 = m / 2, k2 = k / 2, n2 = n / 2;
    return m2 * (k2 > n2 ? k2 : n2) + k2 * n2 + FN(gemms_work)(lv - 1, m2, k2, n2);
}

/* C = A B by lv levels of Strassen-Winograd (fewer where a dimension is odd), C distinct from A, B */
static void FN(gemms)(int lv, size_t m, size_t k, size_t n, const T *A, size_t lda, const T *B, size_t ldb,
                      T *C, size_t ldc, T *w) {
    if (lv <= 0 || m % 2 || k % 2 || n % 2) {
        GEMM(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)m, (int)n, (int)k, 1, A, (int)lda, B, (int)ldb, 0, C,
             (int)ldc);
        return;
    }
    size_t m2 = m / 2, k2 = k / 2, n2 = n / 2;
    const T *A11 = A, *A12 = A + k2, *A21 = A + m2 * lda, *A22 = A21 + k2;
    const T *B11 = B, *B12 = B + n2, *B21 = B + k2 * ldb, *B22 = B21 + n2;
    T *C11 = C, *C12 = C + n2, *C21 = C + m2 * ldc, *C22 = C21 + n2;
    T *X = w, *Y = w + m2 * (k2 > n2 ? k2 : n2), *w2 = Y + k2 * n2;
    int last = lv == 1;
#define GW_REC(a, la, b, lb, c, lc) FN(gemms)(lv - 1, m2, k2, n2, a, la, b, lb, c, lc, w2)
    FN(gw_op)(1, m2, k2, X, k2, A11, lda, A21, lda);   /* S3 = A11 - A21 */
    FN(gw_op)(1, k2, n2, Y, n2, B22, ldb, B12, ldb);   /* T3 = B22 - B12 */
    GW_REC(X, k2, Y, n2, C21, ldc);                     /* P7 = S3 T3 */
    FN(gw_op)(0, m2, k2, X, k2, A21, lda, A22, lda);   /* S1 = A21 + A22 */
    FN(gw_op)(1, k2, n2, Y, n2, B12, ldb, B11, ldb);   /* T1 = B12 - B11 */
    GW_REC(X, k2, Y, n2, C22, ldc);                     /* P5 = S1 T1 */
    FN(gw_op)(1, m2, k2, X, k2, X, k2, A11, lda);      /* S2 = S1 - A11 */
    FN(gw_op)(1, k2, n2, Y, n2, B22, ldb, Y, n2);      /* T2 = B22 - T1 */
    GW_REC(X, k2, Y, n2, C12, ldc);                     /* P6 = S2 T2 */
    FN(gw_op)(1, m2, k2, X, k2, A12, lda, X, k2);      /* S4 = A12 - S2 */
    GW_REC(X, k2, B22, ldb, C11, ldc);                  /* P3 = S4 B22 */
    GW_REC(A11, lda, B11, ldb, X, n2);                  /* P1 = A11 B11 */
    FN(gw_op)(0, m2, n2, C12, ldc, X, n2, C12, ldc);   /* U2 = P1 + P6 */
    FN(gw_op)(0, m2, n2, C21, ldc, C12, ldc, C21, ldc); /* U3 = U2 + P7 */
    FN(gw_op)(0, m2, n2, C12, ldc, C12, ldc, C22, ldc); /* U4 = U2 + P5 */
    FN(gw_op)(0, m2, n2, C22, ldc, C21, ldc, C22, ldc); /* U7 = U3 + P5 = C22 */
    FN(gw_op)(0, m2, n2, C12, ldc, C12, ldc, C11, ldc); /* U5 = U4 + P3 = C12 */
    FN(gw_op)(1, k2, n2, Y, n2, Y, n2, B21, ldb);      /* T4 = T2 - B21 */
    if (last) {
        GEMM(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)m2, (int)n2, (int)k2, -1, A22, (int)lda, Y, (int)n2, 1,
             C21, (int)ldc);                            /* U6 = U3 - A22 T4 = C21 */
        FN(gw_op)(2, m2, n2, C11, ldc, X, n2, NULL, 0);
        GEMM(CblasRowMajor, CblasNoTrans, CblasNoTrans, (int)m2, (int)n2, (int)k2, 1, A12, (int)lda, B21, (int)ldb, 1,
             C11, (int)ldc);                            /* U1 = P1 + A12 B21 = C11 */
    } else {
        GW_REC(A22, lda, Y, n2, C11, ldc);              /* P4 = A22 T4 */
        FN(gw_op)(1, m2, n2, C21, ldc, C21, ldc, C11, ldc); /* U6 = U3 - P4 = C21 */
        GW_REC(A12, lda, B21, ldb, C11, ldc);           /* P2 = A12 B21 */
        FN(gw_op)(0, m2, n2, C11, ldc, C11, ldc, X, n2); /* U1 = P1 + P2 = C11 */
    }
#undef GW_REC
}
