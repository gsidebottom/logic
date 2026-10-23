#!/usr/bin/env python3
"""orbit48: anneal over the GL(4, Z[1/2])^3 orbit of a rank-48 4x4 scheme for
representatives with a low operation floor (step 2 of the rank-48 record
campaign).

Scheme: L (48x16), R (48x16), P (16x48) over Z[1/2] with
Vect(C) = P((L vecA) o (R vecB)), row-major.  Product k has factors
U_k, V_k, W_k (4x4) read from row k of L, row k of R and column k of P.
A sandwich (X, Y, Z) maps U -> X^T U Y^-T, V -> Y^T V Z^-T, W -> X^-1 W Z
and gives another valid scheme computing C = AB directly (no basis change
at run time).  With X, Y, Z in GL(4, Z[1/2]) (determinant +-2^k) every
entry stays dyadic.

Floor (lower bound on PLinOpt's operation count, additions + scalings,
negation free): per side, every distinct row up to sign that is not +-a
unit vector costs at least one operation (a scaled unit costs one
scaling); the output side counts its transpose, +32 (48 - 16).  The
objective is floor_L + floor_R + floor_Pt + 32 + lam * (#coefficients
not in {0, +-1}) (the penalty keeps representatives program-friendly);
entries are confined to {0, +-1/4, +-1/2, +-1, +-2, +-4}.

Moves on one factor M in {X, Y, Z}: row_i += c row_j (c in +-1, +-1/2,
+-2), row swap, row sign, row scale by 2 or 1/2.  Metropolis acceptance,
restarts, the best K distinct points written as sms files and verified
over Q (all 4096 Brent equations).

Arithmetic: all matrices hold integer numerators over the common
denominator 2^DEN (numpy int64); a move that would need a finer
denominator or exceed the entry range is rejected.

Usage: orbit48.py PREFIX OUTDIR [--steps N] [--restarts R] [--seed S]
         [--t0 2.0] [--t1 0.2] [--lam 0.1] [--keep K] [--den 6] [--maxent 4] [--factors XYZ]
"""
import itertools
import os
import sys
import time
from fractions import Fraction as Fr

import numpy as np

DEN = 6  # denominators up to 2^6: entries are multiples of 1/64
SCAL = 1 << DEN


def read_sms(path):
    M = None
    for ln in open(path):
        p = ln.split()
        if M is None:
            if len(p) >= 2 and p[0].isdigit() and p[1].isdigit():
                M = [[Fr(0)] * int(p[1]) for _ in range(int(p[0]))]
            continue
        if len(p) < 3 or (p[0] == "0" and p[1] == "0"):
            break
        M[int(p[0]) - 1][int(p[1]) - 1] = Fr(p[2])
    return M


def to_int(M):
    a = np.zeros((len(M), len(M[0])), dtype=np.int64)
    for i, row in enumerate(M):
        for j, v in enumerate(row):
            x = v * SCAL
            assert x.denominator == 1, f"entry {v} needs a finer denominator than 2^{DEN}"
            a[i, j] = int(x)
    return a


def load(prefix):
    L, R, P = read_sms(prefix + "_L.sms"), read_sms(prefix + "_R.sms"), read_sms(prefix + "_P.sms")
    r = len(L)
    Li, Ri, Pi = to_int(L), to_int(R), to_int(P)
    U = Li.reshape(r, 4, 4)
    V = Ri.reshape(r, 4, 4)
    W = Pi.T.reshape(r, 4, 4)  # column k of P as a 4x4 (row-major over the 16 C entries)
    return U, V, W


def brent_ok(U, V, W):
    """all 4096 Brent equations over Q: sum_k U_k[a] V_k[b] W_k[c] = [b == c... ] (row-major)."""
    r = U.shape[0]
    T = np.einsum("kab,kcd,kef->abcdef", U.astype(object), V.astype(object), W.astype(object))
    s = Fr(1, SCAL ** 3)
    for a, b, c, d, e, f in itertools.product(range(4), repeat=6):
        want = 1 if (b == c and a == e and d == f) else 0
        if T[a, b, c, d, e, f] * s != want:
            return False
    return True


# ---------------------------------------------------------------- floors
def side_floor(rows, lam):
    """rows: (48, 16) numerators over SCAL.  Returns (floor, nonunit_coeffs)."""
    keys = set()
    nonunit = 0
    for row in rows:
        nz = np.flatnonzero(row)
        if nz.size == 0:
            continue
        vals = row[nz]
        nonunit += int(np.count_nonzero(np.abs(vals) != SCAL))
        if nz.size == 1 and abs(int(vals[0])) == SCAL:
            continue  # +-unit vector: free
        sign = 1 if vals[0] > 0 else -1
        keys.add(tuple((sign * row).tolist()))
    return len(keys), nonunit


# side weights and an L/R balance penalty in the objective (defaults: the plain floor)
WEIGHTS = {"wl": 1.0, "wr": 1.0, "wp": 1.0, "wbal": 0.0, "wnz": 0.0}  # wnz: weight on nonzero coefficients


def objective(U, V, W, lam):
    r = U.shape[0]
    fl, nl = side_floor(U.reshape(r, 16), lam)
    fr, nr = side_floor(V.reshape(r, 16), lam)
    fp, np_ = side_floor(W.reshape(r, 16), lam)
    floor = fl + fr + fp + 32
    obj = WEIGHTS["wl"] * fl + WEIGHTS["wr"] * fr + WEIGHTS["wp"] * fp + 32 + lam * (nl + nr + np_) + WEIGHTS["wbal"] * abs(fl - fr)
    if WEIGHTS["wnz"]:
        obj += WEIGHTS["wnz"] * int(np.count_nonzero(U) + np.count_nonzero(V) + np.count_nonzero(W))
    return obj, floor, (fl, fr, fp), nl + nr + np_


# ---------------------------------------------------------------- group
def ident():
    return np.eye(4, dtype=np.int64) * SCAL


def mat_mul(A, B):
    """product of two matrices held over SCAL: (A B)/SCAL, or None when it
    would need a finer denominator or leave the entry range."""
    C = A @ B
    if (C % SCAL != 0).any():
        return None
    C //= SCAL
    if np.abs(C).max() > 16 * SCAL:
        return None
    return C


def apply(U0, V0, W0, X, Xi, Y, Yi, Z, Zi):
    """U = X^T U0 Y^-T, V = Y^T V0 Z^-T, W = X^-1 W0 Z, all over SCAL."""
    def sand(A, F0, B):  # A F0 B for all k, A and B over SCAL -> result over SCAL (divide by SCAL^2)
        C = np.einsum("ab,kbc,cd->kad", A, F0, B)
        if (C % (SCAL * SCAL) != 0).any():
            return None
        return C // (SCAL * SCAL)
    U = sand(X.T, U0, Yi.T)
    V = sand(Y.T, V0, Zi.T)
    W = sand(Xi, W0, Z)
    if U is None or V is None or W is None:
        return None
    return U, V, W


def elementary(kind, i, j, c_num):
    """E and E^-1 over SCAL for row_i += (c_num/SCAL) row_j, swap, sign, scale."""
    E = ident()
    Ei = ident()
    if kind == "add":
        E[i, j] = c_num
        Ei[i, j] = -c_num
    elif kind == "swap":
        E[[i, j]] = E[[j, i]]
        Ei = E.copy()
    elif kind == "sign":
        E[i, i] = -SCAL
        Ei[i, i] = -SCAL
    elif kind == "scale2":
        E[i, i] = 2 * SCAL
        Ei[i, i] = SCAL // 2
    elif kind == "scaleh":
        E[i, i] = SCAL // 2
        Ei[i, i] = 2 * SCAL
    return E, Ei


MAXENT = 4 * SCAL  # entries confined to [-4, 4]
FACTORS = [0, 1, 2]  # which of X, Y, Z the annealer may move (--factors XYZ)


def in_range(U, V, W):
    return max(int(np.abs(U).max()), int(np.abs(V).max()), int(np.abs(W).max())) <= MAXENT


def point_key(U, V, W):
    """identity of a point up to row order and row signs on each side."""
    out = []
    for F in (U, V, W):
        rows = []
        for row in F.reshape(F.shape[0], 16):
            nz = np.flatnonzero(row)
            sign = 1 if nz.size == 0 or row[nz[0]] > 0 else -1
            rows.append(tuple((sign * row).tolist()))
        out.append(tuple(sorted(rows)))
    return hash(tuple(out))


def anneal(U0, V0, W0, steps, t0, t1, lam, rng, log=None, pool=None, pool_floor=10 ** 9, pool_max=400):
    X, Xi, Y, Yi, Z, Zi = (ident() for _ in range(6))
    cur = apply(U0, V0, W0, X, Xi, Y, Yi, Z, Zi)
    obj, floor, sides, nonu = objective(*cur, lam)
    best = (obj, floor, sides, nonu, (X.copy(), Y.copy(), Z.copy()))
    adds = [SCAL, -SCAL, SCAL // 2, -SCAL // 2, 2 * SCAL, -2 * SCAL]
    for step in range(steps):
        T = t0 * (t1 / t0) ** (step / max(1, steps - 1))
        f = int(rng.choice(FACTORS))
        kind = rng.choice(["add", "add", "add", "add", "swap", "sign", "scale2", "scaleh"])
        i, j = rng.integers(4), rng.integers(4)
        if kind in ("add", "swap") and i == j:
            continue
        E, Ei = elementary(kind, i, j, int(rng.choice(adds)))
        mats = [X, Xi, Y, Yi, Z, Zi]
        M, Mi = mats[2 * f], mats[2 * f + 1]
        M2, Mi2 = mat_mul(E, M), mat_mul(Mi, Ei)
        if M2 is None or Mi2 is None:
            continue
        mats2 = list(mats)
        mats2[2 * f], mats2[2 * f + 1] = M2, Mi2
        new = apply(U0, V0, W0, *mats2)
        if new is None or not in_range(*new):
            continue
        obj2, floor2, sides2, nonu2 = objective(*new, lam)
        d = obj2 - obj
        if d <= 0 or rng.random() < np.exp(-d / T):
            X, Xi, Y, Yi, Z, Zi = mats2
            cur, obj, floor, sides, nonu = new, obj2, floor2, sides2, nonu2
            if pool is not None and floor <= pool_floor:
                k = point_key(*cur)
                if k not in pool:
                    if len(pool) < pool_max:
                        pool[k] = (obj, floor, sides, nonu, X.copy(), Y.copy(), Z.copy())
                    else:
                        worst = max(pool, key=lambda kk: (pool[kk][0], pool[kk][1]))
                        if (obj, floor) < (pool[worst][0], pool[worst][1]):
                            del pool[worst]
                            pool[k] = (obj, floor, sides, nonu, X.copy(), Y.copy(), Z.copy())
            if obj < best[0]:
                best = (obj, floor, sides, nonu, (X.copy(), Y.copy(), Z.copy()))
                if log:
                    log(f"    step {step}: floor {floor} sides {sides} nonunit {nonu} obj {obj:.1f}")
    return best


def write_sms(path_prefix, U, V, W):
    r = U.shape[0]

    def fmt(x):
        return str(Fr(int(x), SCAL))

    for name, M in (("L", U.reshape(r, 16)), ("R", V.reshape(r, 16))):
        with open(f"{path_prefix}_{name}.sms", "w") as f:
            f.write(f"{r} 16 R\n")
            for i in range(r):
                for j in range(16):
                    if M[i, j]:
                        f.write(f"{i + 1} {j + 1} {fmt(M[i, j])}\n")
            f.write("0 0 0\n")
    Pm = W.reshape(r, 16).T
    with open(f"{path_prefix}_P.sms", "w") as f:
        f.write(f"16 {r} R\n")
        for i in range(16):
            for k in range(r):
                if Pm[i, k]:
                    f.write(f"{i + 1} {k + 1} {fmt(Pm[i, k])}\n")
        f.write("0 0 0\n")


def main():
    args = sys.argv[1:]

    def opt(name, default, cast=float):
        if name in args:
            i = args.index(name)
            v = cast(args[i + 1])
            del args[i:i + 2]
            return v
        return default

    steps = opt("--steps", 20000, int)
    restarts = opt("--restarts", 8, int)
    seed = opt("--seed", 1, int)
    t0, t1 = opt("--t0", 2.0), opt("--t1", 0.2)
    lam = opt("--lam", 0.1)
    keep = opt("--keep", 8, int)
    pool_floor = opt("--pool-floor", 150, int)
    global MAXENT, FACTORS
    FACTORS = ["XYZ".index(ch) for ch in opt("--factors", "XYZ", str)]  # e.g. Y: keep P fixed
    MAXENT = int(opt("--maxent", MAXENT // SCAL, float) * SCAL)  # entry cap (default 4)
    for k in ("wl", "wr", "wp", "wbal", "wnz"):
        WEIGHTS[k] = opt("--" + k, WEIGHTS[k])
    prefix, outdir = args[0], args[1]
    os.makedirs(outdir, exist_ok=True)
    U0, V0, W0 = load(prefix)
    assert brent_ok(U0, V0, W0), "input scheme fails Brent over Q"
    obj0, floor0, sides0, nonu0 = objective(U0, V0, W0, lam)
    print(f"input: floor {floor0} = {sides0} + 32, non-unit coefficients {nonu0}, objective {obj0:.1f}", flush=True)
    rng = np.random.default_rng(seed)
    pool = {}
    t0s = time.time()

    def dump():
        ranked = sorted(pool.values(), key=lambda v: (v[0], v[1]))[:keep]
        rows = ["rank,floor,fl,fr,fp,nonunit,objective,prefix"]
        for n, (obj, floor, sides, nonu, X, Y, Z) in enumerate(ranked):
            Xi, Yi, Zi = (np.rint(np.linalg.inv(M / SCAL) * SCAL).astype(np.int64) for M in (X, Y, Z))
            res = apply(U0, V0, W0, X, Xi, Y, Yi, Z, Zi)
            assert res is not None and brent_ok(*res), "candidate fails Brent"
            pre = os.path.join(outdir, f"cand{n:03d}")
            write_sms(pre, *res)
            rows.append(f"{n},{floor},{sides[0]},{sides[1]},{sides[2]},{nonu},{obj:.1f},{pre}")
        open(os.path.join(outdir, "candidates.csv"), "w").write("\n".join(rows) + "\n")
        return rows

    for rs in range(restarts):
        best = anneal(U0, V0, W0, steps, t0, t1, lam, rng, log=None, pool=pool, pool_floor=pool_floor)
        obj, floor, sides, nonu, (X, Y, Z) = best
        print(f"restart {rs}: best floor {floor} sides {sides} non-unit {nonu} obj {obj:.1f}; pool {len(pool)} distinct points ({time.time() - t0s:.0f}s)", flush=True)
        dump()
    rows = dump()
    print(f"pool: {len(pool)} distinct points with floor <= {pool_floor}; wrote {len(rows) - 1} candidates", flush=True)


if __name__ == "__main__":
    main()
