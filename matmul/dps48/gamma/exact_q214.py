"""The orbit's gamma_{inf,2} minimum (21.4073, the Q(sqrt2) point of the other roles) exactly.

slp/g214d_{L,R,P}.slp hold it as the direct-sum programs that were measured, with floating-point
constants (0.500000002463738, 0.41421356...).  Here every coefficient is snapped to a + b sqrt2
with a, b in (1/4) Z (the snap is unique: distinct grid points differ by more than 7e-3 and the
residuals are below 1e-6), the Brent equations are checked exactly in Q(sqrt2) (integer arithmetic
on the two components), and the growth factors are evaluated exactly where they lie in Q(sqrt2)
and to 40 digits otherwise.  The exact scheme is written as three sparse files
"row col a b" (1-based, entry a + b sqrt2, header "rows cols Q(sqrt2)") and one readable listing.

  python3 exact_q214.py [out_dir]            (default: this directory)
"""
import os, sys
from fractions import Fraction as F
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "fastmm"))
import growth

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else HERE
S2 = np.sqrt(2.0)
N, RK = 4, 48

L, R, P = growth.from_slp(os.path.join(HERE, "slp", "g214d"), N * N, RK)
f = lambda M: np.array([[float(x) for x in row] for row in M])
L, R, P = f(L), f(R), f(P)

# --- snap to (a + b sqrt2) / 4 with integer a, b ----------------------------------------------
GRID = [(a, b) for a in range(-16, 17) for b in range(-16, 17)]
GVAL = np.array([(a + b * S2) / 4 for a, b in GRID])

def snap(M):
    """integer arrays A, B with M ~ (A + B sqrt2) / 4; asserts the snap is tight"""
    A = np.zeros(M.shape, dtype=np.int64); B = np.zeros(M.shape, dtype=np.int64)
    worst = 0.0
    for idx, c in np.ndenumerate(M):
        k = int(np.argmin(np.abs(GVAL - c)))
        worst = max(worst, abs(GVAL[k] - c))
        A[idx], B[idx] = GRID[k]
    assert worst < 1e-6, worst
    return A, B, worst

LA, LB, wl = snap(L); RA, RB, wr = snap(R); PA, PB, wp = snap(P)
print(f"snap residuals: L {wl:.1e} R {wr:.1e} P {wp:.1e}")

# --- Brent equations exactly: sum_r L[r,i] R[r,j] P[k,r] = T[i,j,k], components of sqrt2 ------
# (A + B s)(C + D s) = (AC + 2BD) + (AD + BC) s, s^2 = 2.  Scaled by 4^3 = 64.
def mul(xa, xb, ya, yb):
    return xa * ya + 2 * xb * yb, xa * yb + xb * ya
def prod3(ia, ib, ja, jb, ka, kb):
    ra, rb = mul(ia, ib, ja, jb)
    return mul(ra, rb, ka, kb)
Ta = np.zeros((16, 16, 16), dtype=np.int64); Tb = np.zeros((16, 16, 16), dtype=np.int64)
for r in range(RK):
    la, lb = LA[r][:, None, None], LB[r][:, None, None]
    ra_, rb_ = RA[r][None, :, None], RB[r][None, :, None]
    pa, pb = PA[:, r][None, None, :], PB[:, r][None, None, :]
    a, b = prod3(la, lb, ra_, rb_, pa, pb)
    Ta += a; Tb += b
W = np.zeros((16, 16, 16), dtype=np.int64)
for i in range(N):
    for j in range(N):
        for l in range(N):
            W[i * N + j, j * N + l, i * N + l] = 1
ok = np.array_equal(Ta, 64 * W) and not Tb.any()
print("Brent equations in Q(sqrt2):", "EXACT" if ok else "FAIL")
assert ok

# --- exact norms and growth factors --------------------------------------------------------------
def q(a, b):              # (a + b sqrt2)/4 as a pair of Fractions
    return F(int(a), 4), F(int(b), 4)
def qval(x):              # float of a Q(sqrt2) pair
    return float(x[0]) + float(x[1]) * S2
def qabs(x):
    return x if qval(x) >= 0 else (-x[0], -x[1])
def qadd(x, y):
    return x[0] + y[0], x[1] + y[1]
def qmul(x, y):
    return x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0]
def qsqrt(x):
    """sqrt of a + b sqrt2 inside Q(sqrt2) if it exists: (u + v sqrt2)^2 = u^2 + 2v^2 + 2uv sqrt2"""
    a, b = x
    # try v = 0 or u = 0, and the general case via the norm: (u^2 - 2 v^2)^2 = a^2 - 2 b^2
    from math import isqrt
    def rsqrt(fr):   # exact rational sqrt or None
        if fr < 0: return None
        n, d = fr.numerator, fr.denominator
        rn, rd = isqrt(n), isqrt(d)
        return F(rn, rd) if rn * rn == n and rd * rd == d else None
    if b == 0:
        s = rsqrt(a)
        if s is not None: return (s, F(0))
        s = rsqrt(a / 2)
        if s is not None: return (F(0), s)
        return None
    nrm = rsqrt(a * a - 2 * b * b)
    if nrm is None: return None
    for sign in (1, -1):
        u2 = (a + sign * nrm) / 2
        u = rsqrt(u2)
        if u is None or u == 0: continue
        v = b / (2 * u)
        if u * u + 2 * v * v == a and 2 * u * v == b:
            return (u, v)
    return None

def fmt(x):
    a, b = x
    if b == 0: return str(a)
    if a == 0: return f"{b}*sqrt2" if b != 1 else "sqrt2"
    sb = f"+{b}*sqrt2" if b > 0 else f"{b}*sqrt2"
    return f"{a}{sb}"

rows = lambda A, B: [[q(A[i, j], B[i, j]) for j in range(A.shape[1])] for i in range(A.shape[0])]
Lq, Rq, Pq = rows(LA, LB), rows(RA, RB), rows(PA, PB)
one_norm = lambda row: __import__("functools").reduce(qadd, (qabs(x) for x in row), (F(0), F(0)))
sq_norm = lambda row: __import__("functools").reduce(qadd, (qmul(x, x) for x in row), (F(0), F(0)))

l1 = [one_norm(r) for r in Lq]; r1 = [one_norm(r) for r in Rq]
l2 = [sq_norm(r) for r in Lq]; r2 = [sq_norm(r) for r in Rq]
# gamma_{inf,inf} = max_j sum_i |p_ji| |L_i|_1 |R_i|_1, exactly in Q(sqrt2)
g_ii = []
for j in range(16):
    acc = (F(0), F(0))
    for i in range(RK):
        acc = qadd(acc, qmul(qabs(Pq[j][i]), qmul(l1[i], r1[i])))
    g_ii.append(acc)
g_ii_max = max(g_ii, key=qval)
print("gamma_{inf,inf} =", fmt(g_ii_max), "=", qval(g_ii_max))
# gamma_{inf,2} = max_j sum_i |p_ji| |L_i|_2 |R_i|_2: the row norms' squares are in Q(sqrt2)
sq_in_field = all(qsqrt(x) is not None for x in l2) and all(qsqrt(x) is not None for x in r2)
print("row 2-norms of L and R lie in Q(sqrt2):", sq_in_field)
try:
    import mpmath
    mpmath.mp.dps = 40
    s2 = mpmath.sqrt(2)
    val = lambda x: mpmath.mpf(x[0].numerator) / x[0].denominator + mpmath.mpf(x[1].numerator) / x[1].denominator * s2
    g_i2 = []
    for j in range(16):
        acc = mpmath.mpf(0)
        for i in range(RK):
            acc += abs(val(Pq[j][i])) * mpmath.sqrt(val(l2[i])) * mpmath.sqrt(val(r2[i]))
        g_i2.append(acc)
    gm = max(g_i2)
    print("gamma_{inf,2} =", mpmath.nstr(gm, 25))
    print("  identify:", mpmath.identify(gm, ["sqrt(2)"]), " squared:", mpmath.identify(gm ** 2, ["sqrt(2)"]))
    print("  per output:", " ".join(mpmath.nstr(x, 10) for x in g_i2))
    dist = sorted(set(mpmath.nstr(x, 12) for x in g_i2))
    print("  distinct per-output values:", dist)
    # gamma_2 = sum_i |L_i|_2 |R_i|_2 |P_{*,i}|_2
    p2 = [sq_norm([Pq[j][i] for j in range(16)]) for i in range(RK)]
    g2 = sum(mpmath.sqrt(val(l2[i])) * mpmath.sqrt(val(r2[i])) * mpmath.sqrt(val(p2[i])) for i in range(RK))
    print("gamma_2 =", mpmath.nstr(g2, 20), " identify:", mpmath.identify(g2, ["sqrt(2)"]))
    print("row norms^2 of L:", sorted(set(fmt(x) for x in l2)), " of R:", sorted(set(fmt(x) for x in r2)), " of P columns:", sorted(set(fmt(x) for x in p2)))
except ImportError:
    print("mpmath not available; gamma_{inf,2} from floats:", max((np.abs(P) @ (np.linalg.norm(L, axis=1) * np.linalg.norm(R, axis=1)))))

# gamma_{inf,2} in closed form: every |R_i|^2 is the same element of Q(sqrt2) and every |L_i|^2 is
# rational, so each output's sum is (an element of Q(sqrt2)) x sqrt(|R_i|^2); the worst output's
# coefficient is collected exactly and the square of the result lies in Q(sqrt2).
r2set = set(r2)
assert len(r2set) == 1, [fmt(x) for x in r2set]
r2c = next(iter(r2set))
from math import isqrt
coef = []                       # per output: sum_i |p_ji| sqrt(|L_i|^2), with sqrt(|L_i|^2) rational or rational * sqrt2
for j in range(16):
    acc = (F(0), F(0))
    for i in range(RK):
        a, b = l2[i]
        assert b == 0
        n, d = a.numerator, a.denominator
        if isqrt(n) ** 2 == n and isqrt(d) ** 2 == d:
            s = (F(isqrt(n), isqrt(d)), F(0))
        else:
            h = a / 2; n, d = h.numerator, h.denominator
            assert isqrt(n) ** 2 == n and isqrt(d) ** 2 == d, a
            s = (F(0), F(isqrt(n), isqrt(d)))
        acc = qadd(acc, qmul(qabs(Pq[j][i]), s))
    coef.append(acc)
print("gamma_{inf,2}(j) = c_j * sqrt(" + fmt(r2c) + ") with c_j in", sorted(set(fmt(c) for c in coef)))
cmax = max(coef, key=lambda c: qval(c) * np.sqrt(qval(r2c)))
sq = qmul(qmul(cmax, cmax), r2c)
print(f"gamma_{{inf,2}} = ({fmt(cmax)}) * sqrt({fmt(r2c)}) = sqrt({fmt(sq)}) = {qval(cmax) * np.sqrt(qval(r2c)):.10f}; exponent log_4 = {np.log(qval(cmax) * np.sqrt(qval(r2c))) / np.log(4):.4f}")

# --- coefficient census and files ------------------------------------------------------------------
for name, M in (("L", Lq), ("R", Rq), ("P", Pq)):
    seen = {}
    for row in M:
        for x in row:
            if x != (0, 0):
                seen[fmt(qabs(x))] = seen.get(fmt(qabs(x)), 0) + 1
    print(f"{name}: nonzeros {sum(seen.values())}, |coefficients| " + ", ".join(f"{k} x{v}" for k, v in sorted(seen.items(), key=lambda kv: kv[1], reverse=True)))

os.makedirs(OUT, exist_ok=True)
for name, A, B in (("L", LA, LB), ("R", RA, RB), ("P", PA, PB)):
    with open(os.path.join(OUT, f"g214_exact_{name}.txt"), "w") as fh:
        fh.write(f"{A.shape[0]} {A.shape[1]} Q(sqrt2)\n")
        for (i, j), a in np.ndenumerate(A):
            b = B[i, j]
            if a or b:
                fh.write(f"{i + 1} {j + 1} {F(int(a), 4)} {F(int(b), 4)}\n")
        fh.write("0 0 0 0\n")
with open(os.path.join(OUT, "g214_exact.txt"), "w") as fh:
    fh.write("# <4x4x4:48> scheme at the de Groote orbit's gamma_{inf,2} minimum 21.4073 (Q(sqrt2) point, other roles)\n")
    fh.write("# vec(C) = P ((L vec A) o (R vec B)), row-major vectorization; entries a+b*sqrt2 exact; Brent equations checked exactly in Q(sqrt2)\n")
    for name, M in (("L", Lq), ("R", Rq), ("P", Pq)):
        fh.write(f"# {name} ({len(M)} x {len(M[0])})\n")
        for row in M:
            fh.write(" ".join(fmt(x) if x != (0, 0) else "0" for x in row) + "\n")
print("written", OUT + "/g214_exact_{L,R,P}.txt and g214_exact.txt")
