#!/usr/bin/env python3
"""Reduce a matrix multiplication scheme by the dependencies of its Kronecker products (exact, over Q).

In direction d (slots r, c the two others) product t contributes K_t (x) f_t, K_t the Kronecker product of
its slot-r and slot-c factors and f_t its slot-d factor.  A dependency sum_t mu_t K_t = 0 with mu_j != 0
gives K_j = -sum_{t != j} (mu_t / mu_j) K_t, so product j can be dropped after f_t -= (mu_t / mu_j) f_j.
Using every dependency leaves dim span{K_t} products.  This is the removal step of a 2-reducible
decomposition in the sense of Khoruzhii, Serafin, Gelss, Pokutta (LITA, github.com/khoruzhii/lita).

usage: kron_reduce.py SCHEME.json D OUT.json [--pivots j1,j2,...]

--pivots names the products to drop (one per dependency; any set on which the dependencies are
independent).  Every choice drops as many products as there are dependencies, but other products can
lose their slot-D factor in the same fold, and which do depends on the choice (kron_kill.py searches
it).  Products left with a zero factor are removed and reported.

Steps.  (1) The dependencies modulo 2^31 - 1 from the Gram matrix, in echelon form; (2) the same modulo
further primes on the union of their supports, combined by the Chinese remainder theorem and lifted to Q;
(3) each dependency verified EXACTLY on the Kronecker products in integer arithmetic; (4) the fold;
(5) the Brent equations of the input and of the output verified EXACTLY: by a direct route when every
partial sum stays below 2^53 (float64 and int64, two contraction orders), and always by a modular route
(two contraction orders on disjoint sets of primes whose product exceeds twice a proven bound on every
entry, so agreement modulo all of them is equality); (6) a corrupted copy of the output must be rejected.
"""
import sys, os, json, math, time
from fractions import Fraction
import numpy as np
RC = [(1, 2), (0, 2), (0, 1)]

def is_prime(n):
    if n < 2: return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0: return n == q
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13):                # deterministic below 3.4e12
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

def primes_below(top, count):
    out = []; q = top - 1
    while len(out) < count:
        if is_prime(q): out.append(q)
        q -= 1
    return out

BIGP = primes_below(2 ** 31, 64)                  # for the dependencies; the first is 2^31 - 1
SMALLP = primes_below(2 ** 20, 1200)              # for the Brent equations (float64 products stay exact)
P = BIGP[0]

def frac(x): return Fraction(x) if isinstance(x, str) else Fraction(int(x)) if float(x) == int(x) else Fraction(str(x))

def load(path):
    d = json.load(open(path))
    n = tuple(d['n'])
    F = [[[frac(x) for x in row] for row in d[k]] for k in ('u', 'v', 'w')]
    assert len(F[0]) == len(F[1]) == len(F[2]) == d['m']
    assert len(F[0][0]) == n[0] * n[1] and len(F[1][0]) == n[1] * n[2] and len(F[2][0]) == n[2] * n[0]
    return n, F

def lcm_den(rows):
    den = 1
    for row in rows:
        for f in row:
            if f.denominator != 1: den = den * f.denominator // math.gcd(den, f.denominator)
    return den

def gram_mod(A, p=P):
    """A A^T modulo p < 2^31 for an integer matrix with entries of any size (16-bit split, no int64 overflow)."""
    A = np.array([[int(x) % p for x in row] for row in A], dtype=np.int64)
    lo, hi = A & 0xFFFF, A >> 16
    ll = lo.dot(lo.T) % p; hh = hi.dot(hi.T) % p; lh = lo.dot(hi.T) % p
    return (ll + ((lh + lh.T) % p) * (1 << 16) % p + hh * ((1 << 32) % p) % p) % p

def left_null_mod(G, p=P):
    """Left null vectors of G modulo p, in reduced echelon form.  Returns rank, vectors, pivots."""
    m = G.shape[0]
    M = np.concatenate([G % p, np.eye(m, dtype=np.int64)], axis=1)
    row = 0
    for col in range(m):
        nz = np.nonzero(M[row:, col])[0]
        if nz.size == 0: continue
        piv = row + int(nz[0])
        if piv != row: M[[row, piv]] = M[[piv, row]]
        inv = pow(int(M[row, col]), p - 2, p)
        M[row] = (M[row] * inv) % p
        f = M[:, col].copy(); f[row] = 0
        idx = np.nonzero(f)[0]
        if idx.size: M[idx] = (M[idx] - np.outer(f[idx], M[row])) % p
        row += 1
    N = [[int(x) for x in M[i, m:]] for i in range(row, m)]
    piv = []
    for i in range(len(N)):                      # echelon form among the null vectors (plain Python, few rows)
        j = next(c for c in range(m) if N[i][c] and c not in piv)
        inv = pow(N[i][j], p - 2, p)
        N[i] = [x * inv % p for x in N[i]]
        for k in range(len(N)):
            if k != i and N[k][j]:
                f = N[k][j]
                N[k] = [(x - f * y) % p for x, y in zip(N[k], N[i])]
        piv.append(j)
    return row, N, piv

def normalize_on(N, cols, p):
    """The basis of span(N) modulo p that is the identity on the columns cols, or None."""
    k = len(N)
    B = [[N[i][c] % p for c in cols] + [int(i == j) for j in range(k)] for i in range(k)]
    for col in range(k):
        pr = next((r for r in range(col, k) if B[r][col]), None)
        if pr is None: return None
        B[col], B[pr] = B[pr], B[col]
        inv = pow(B[col][col], p - 2, p)
        B[col] = [x * inv % p for x in B[col]]
        for r in range(k):
            if r != col and B[r][col]:
                f = B[r][col]
                B[r] = [(x - f * y) % p for x, y in zip(B[r], B[col])]
    inv = [row[k:] for row in B]
    return [[sum(inv[i][j] * N[j][c] for j in range(k)) % p for c in range(len(N[0]))] for i in range(k)]

def ratrec(a, M):
    """The fraction r / s = a modulo M with |r|, |s| <= sqrt(M / 2), or None."""
    B = math.isqrt((M - 1) // 2)
    r0, r1, s0, s1 = M, a % M, 0, 1
    while r1 > B:
        q = r0 // r1
        r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    if s1 == 0 or abs(s1) > B or math.gcd(r1, abs(s1)) != 1: return None
    return Fraction(r1, s1)

def lift(rows, J, N0, piv, maxprimes=48):
    """Null vectors over Q on the products J: N0 holds their residues modulo BIGP[0] (identity on piv)."""
    pos = {t: i for i, t in enumerate(J)}
    cols = [pos[j] for j in piv]
    rowsJ = [[rows[s][t] for t in J] for s in (0, 1)]
    res = [[v[t] for t in J] for v in N0]; M = BIGP[0]; prev = None; used = 1; bad = 0
    for p in BIGP[1:maxprimes]:
        cand = [[ratrec(x, M) if x else Fraction(0) for x in v] for v in res]
        if all(x is not None for v in cand for x in v):
            if cand == prev: return cand, used
            prev = cand
        else: prev = None
        t0 = time.time()
        rk, Nj, pj = left_null_mod((gram_mod(rowsJ[0], p) * gram_mod(rowsJ[1], p)) % p, p)
        Nn = normalize_on(Nj, cols, p) if len(Nj) == len(N0) else None
        if Nn is None:
            bad += 1
            print(f'    prime {p}: {len(Nj)} null vectors on the support, skipped', flush=True)
            if bad >= 3: return None, used
            continue
        inv = pow(M % p, p - 2, p)
        res = [[a + M * ((b - a) * inv % p) for a, b in zip(va, vb)] for va, vb in zip(res, Nn)]
        M *= p; used += 1
        print(f'    prime {p}: {used} primes, modulus of {M.bit_length()} bits ({time.time() - t0:.1f} s)', flush=True)
    return None, used

def dep_exact(lam, rowsJ):
    """sum_t lam_t (U_t (x) V_t) = 0 exactly, in integer arithmetic (numpy object arrays)."""
    L = 1
    for x in lam: L = L * x.denominator // math.gcd(L, x.denominator)
    c = [int(x * L) for x in lam]
    nz = [i for i, x in enumerate(c) if x]
    A = np.array([[c[i] * a for a in rowsJ[0][i]] for i in nz], dtype=object)
    B = np.array([rowsJ[1][i] for i in nz], dtype=object)
    T = A.T.dot(B)
    return all(x == 0 for x in T.flat), L

def prepare(F):
    D = [lcm_den(M) for M in F]
    I = [[[int(x * D[s]) for x in row] for row in F[s]] for s in range(3)]
    mx = [[max((abs(x) for x in row), default=0) for row in M] for M in I]
    B = sum(a * b * c for a, b, c in zip(*mx))    # every entry of sum_t U_t (x) V_t (x) W_t is at most B in absolute value
    return D, I, B, D[0] * D[1] * D[2]

def widx_of(conv, n0, n2): return (lambda i, k: i * n2 + k) if conv == 'ik' else (lambda i, k: k * n0 + i)

def direct(n, I, DD, conv):
    """Both contractions in machine arithmetic; valid when every partial sum is below 2^53."""
    n0, n1, n2 = n; widx = widx_of(conv, n0, n2)
    Uf, Vf, Wf = (np.array(M, dtype=np.float64) for M in I)
    Ui, Vi, Wi = (np.array(M, dtype=np.int64) for M in I)
    bad = 0
    for q in range(n0 * n1):                      # contraction 1: fix the slot-0 coordinate, float64 BLAS
        i, j = divmod(q, n1)
        idx = np.nonzero(Uf[:, q])[0]
        Mx = (Uf[idx, q][:, None] * Vf[idx]).T.dot(Wf[idx]) if idx.size else np.zeros((n1 * n2, n0 * n2))
        E = np.zeros((n1 * n2, n0 * n2))
        for k in range(n2): E[j * n2 + k, widx(i, k)] = DD
        bad += int(np.count_nonzero(Mx != E))
    if bad: return False, f'float64 contraction FAILS ({bad} entries differ)'
    for i in range(n0):                           # contraction 2: fix the slot-2 coordinate, int64
        for k in range(n2):
            r = widx(i, k)
            idx = np.nonzero(Wi[:, r])[0]
            Mx = (Ui[idx] * Wi[idx, r][:, None]).T.dot(Vi[idx]) if idx.size else np.zeros((n0 * n1, n1 * n2), dtype=np.int64)
            E = np.zeros((n0 * n1, n1 * n2), dtype=np.int64)
            for j in range(n1): E[i * n1 + j, j * n2 + k] = DD
            if not np.array_equal(Mx, E): return False, 'float64 contraction matches, int64 contraction FAILS'
    return True, 'float64 and int64 contractions EXACT MATCH'

def modular(n, I, DD, B, conv):
    """Both contractions modulo primes near 2^20; each on its own set of primes with product > 2 (B + DD)."""
    n0, n1, n2 = n; widx = widx_of(conv, n0, n2); m = len(I[0])
    need = 2 * (B + DD); sets = [[], []]; prod = [1, 1]; k = 0
    while min(prod) <= need:
        s = k % 2; sets[s].append(SMALLP[k]); prod[s] *= SMALLP[k]; k += 1
    assert m * (SMALLP[0] - 1) ** 2 < 2 ** 53, 'float64 products would not be exact'
    for s in (0, 1):
        for p in sets[s]:
            Uf, Vf, Wf = (np.array([[x % p for x in row] for row in M], dtype=np.float64) for M in I)
            ddp = float(DD % p)
            if s == 0:
                for q in range(n0 * n1):          # contraction 1: fix the slot-0 coordinate
                    i, j = divmod(q, n1)
                    idx = np.nonzero(Uf[:, q])[0]
                    Mx = np.fmod(np.fmod(Uf[idx, q][:, None] * Vf[idx], p).T.dot(Wf[idx]), p) if idx.size else np.zeros((n1 * n2, n0 * n2))
                    E = np.zeros((n1 * n2, n0 * n2))
                    for k2 in range(n2): E[j * n2 + k2, widx(i, k2)] = ddp
                    if not np.array_equal(Mx, E): return False, f'contraction 1 FAILS modulo {p}'
            else:
                for i in range(n0):               # contraction 2: fix the slot-2 coordinate
                    for k2 in range(n2):
                        r = widx(i, k2)
                        idx = np.nonzero(Wf[:, r])[0]
                        Mx = np.fmod(np.fmod(Uf[idx] * Wf[idx, r][:, None], p).T.dot(Vf[idx]), p) if idx.size else np.zeros((n0 * n1, n1 * n2))
                        E = np.zeros((n0 * n1, n1 * n2))
                        for j in range(n1): E[i * n1 + j, j * n2 + k2] = ddp
                        if not np.array_equal(Mx, E): return False, f'contraction 2 FAILS modulo {p}'
    return True, f'both contractions EXACT MATCH modulo {len(sets[0])} + {len(sets[1])} primes (each product above 2 (B + DD), {need.bit_length()} bits)'

def brent(n, F, tag, convs=('ik', 'ki')):
    """Exact check of sum_t u_t (x) v_t (x) w_t = <n0, n1, n2>.  Returns the index convention of slot 2
    ('ik' or 'ki') under which it holds, or None."""
    D, I, B, DD = prepare(F)
    fits = B + DD < 2 ** 53
    print(f'  [{tag}] m = {len(I[0])}; common denominators {D}; bound B on every entry: {B.bit_length()} bits ({"below" if fits else "NOT below"} 2^53)', flush=True)
    good = []
    for conv in convs:
        t0 = time.time()
        okm, msgm = modular(n, I, DD, B, conv)
        t1 = time.time()
        line = f'  [{tag}] slot-2 index convention {conv}: modular route: {msgm} ({t1 - t0:.1f} s)'
        if fits:
            okd, msgd = direct(n, I, DD, conv)
            line += f'; direct route: {msgd} ({time.time() - t1:.1f} s)'
            if okd != okm: print(line, flush=True); raise SystemExit('the two verification routes DISAGREE')
        print(line, flush=True)
        if okm: good.append(conv)
    return good[0] if good else None

def out_val(f): return int(f) if f.denominator == 1 else f'{f.numerator}/{f.denominator}'

if __name__ == '__main__':
    args = sys.argv[1:]; want = None
    if '--pivots' in args:
        i = args.index('--pivots'); want = [int(x) for x in args[i + 1].split(',')]; del args[i:i + 2]
    path, d, out = args[0], int(args[1]), args[2]
    n, F = load(path); m = len(F[0]); r, c = RC[d]
    print(f'{os.path.basename(path)}: shape {n}, m = {m}, direction {d} (Kronecker products of slots {r}, {c})', flush=True)
    conv = brent(n, F, 'input')
    if conv is None: raise SystemExit('the INPUT does not verify')
    sc = []; rows = []
    for s in (r, c):
        sr = []; ir = []
        for row in F[s]:
            den = 1
            for f in row: den = den * f.denominator // math.gcd(den, f.denominator)
            sr.append(den); ir.append([int(f * den) for f in row])
        sc.append(sr); rows.append(ir)
    t0 = time.time()
    rank, N, piv = left_null_mod((gram_mod(rows[0]) * gram_mod(rows[1])) % P)
    print(f'  Gram rank modulo {P}: {rank} of {m}; {len(N)} dependencies; pivots {piv} ({time.time() - t0:.1f} s)', flush=True)
    if not N: raise SystemExit('no dependency: nothing to reduce')
    if want is not None:
        if len(want) != len(N) or len(set(want)) != len(want): raise SystemExit(f'--pivots needs {len(N)} distinct products')
        Nn = normalize_on(N, want, P)
        if Nn is None: raise SystemExit('the dependencies are not independent on the prescribed pivots')
        N, piv = Nn, list(want)
        print(f'  prescribed pivots {piv}', flush=True)
    J = sorted(set(t for v in N for t in range(m) if v[t]))
    print(f'  supports {[sum(1 for x in v if x) for v in N]}, union {len(J)} products', flush=True)
    lam, used = lift(rows, J, N, piv)
    if lam is None and len(J) < m:
        print('  no lift on the union of the supports; retrying on all products', flush=True)
        J = list(range(m)); lam, used = lift(rows, J, N, piv)
    if lam is None: raise SystemExit('rational reconstruction FAILED')
    rowsJ = [[rows[s][t] for t in J] for s in (0, 1)]
    deps = []
    for v, j in zip(lam, piv):
        t0 = time.time()
        exact, L = dep_exact(v, rowsJ)
        mu = {t: x * sc[0][t] * sc[1][t] for t, x in zip(J, v) if x}
        vals = sorted(set(mu.values()))
        hmax = max(max(abs(x.numerator), x.denominator) for x in mu.values())
        print(f'  dependency with pivot {j}: {len(mu)} products, lifted from {used} primes, EXACT over Q on the Kronecker products: {exact} ({time.time() - t0:.1f} s); common denominator of {L.bit_length()} bits; {len(vals)} distinct coefficients, largest numerator or denominator {hmax}; products {sorted(mu)[:16]}{"..." if len(mu) > 16 else ""}', flush=True)
        if not exact: raise SystemExit('dependency does not hold exactly')
        deps.append((j, mu))
    pivs = set(j for j, _ in deps)
    for j, mu in deps: assert all(t not in pivs or t == j for t in mu), 'pivots not independent'
    Fd = [list(row) for row in F[d]]
    for j, mu in deps:
        fj = F[d][j]
        for t, x in mu.items():
            if t == j: continue
            q = x / mu[j]
            Fd[t] = [a - q * b for a, b in zip(Fd[t], fj)]
    keep = [t for t in range(m) if t not in pivs]
    dead = [t for t in keep if not any(Fd[t])]
    if dead:
        print(f'  {len(dead)} further products are left with a zero slot-{d} factor and are removed: {dead}', flush=True)
        gone = set(dead); keep = [t for t in keep if t not in gone]
    R = [[M[t] for t in keep] for M in F]; R[d] = [Fd[t] for t in keep]
    print(f'  folded: {m} -> {len(keep)} products ({len(pivs)} by the dependencies, {len(dead)} left with a zero factor)', flush=True)
    conv2 = brent(n, R, 'output', convs=(conv,))
    bad = [[list(row) for row in M] for M in R]
    t = len(keep) // 2; s = next(i for i, x in enumerate(bad[d][t]) if x); bad[d][t][s] += 1
    ctrl = brent(n, bad, 'negative control: one entry of the output changed', convs=(conv,))
    print(f'  RESULT: input verifies ({conv}); output with {len(keep)} products {"VERIFIES EXACTLY" if conv2 else "DOES NOT VERIFY"}; corrupted copy {"REJECTED" if ctrl is None else "ACCEPTED (checker is broken)"}', flush=True)
    if conv2 and ctrl is None:
        json.dump({'n': list(n), 'm': len(keep), 'z2': False, 'u': [[out_val(x) for x in row] for row in R[0]],
                   'v': [[out_val(x) for x in row] for row in R[1]], 'w': [[out_val(x) for x in row] for row in R[2]]}, open(out, 'w'))
        json.dump({'source': os.path.basename(path), 'direction': d, 'dropped': sorted(pivs), 'also_zero': dead,
                   'dependencies': [{'pivot': j, 'mu': {str(t): out_val(x) for t, x in sorted(mu.items())}} for j, mu in deps]},
                  open(os.path.splitext(out)[0] + '.deps.json', 'w'))
        print(f'  written {out}', flush=True)
