#!/usr/bin/env python3
"""Probe the rational <4x4x4:48> (Dumas-Pernet-Sedoglavic, arXiv
2506.13242, the de-complexified AlphaEvolve scheme) for fewer
operations than their PLinOpt SLP: L = 104 adds, R = 84 adds + 1
shift, P = 119 adds + 33 shifts (341 ops total).

  probe48.py verify              exact proof: all 4096 Brent equations
                                 over Q (Fractions, no sampling)
  probe48.py baseline            deterministic greedy CSE counts
  probe48.py storm SECONDS [SEED]
                                 restart storm on L and R: random
                                 tie-breaks x signed-permutation
                                 isotropy twists; prints improvements
The .sms matrices live in matmul/dps48/ (fetched from the PLinOpt
repo's data/ directory).
"""
import random
import sys
import time
from fractions import Fraction

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from slp import greedy_slp

HERE = __file__.rsplit("/", 1)[0]
R_PROD = 48


def parse_sms(path):
    rows = cols = None
    mat = None
    for ln in open(path):
        ln = ln.strip()
        if not ln or ln.startswith("#"):
            continue
        parts = ln.split()
        if rows is None:
            rows, cols = int(parts[0]), int(parts[1])
            mat = [[Fraction(0)] * cols for _ in range(rows)]
            continue
        i, j, v = int(parts[0]), int(parts[1]), Fraction(parts[2])
        if i == 0 and j == 0:
            break
        mat[i - 1][j - 1] = v
    return mat


def load(gauge=True):
    L = parse_sms(f"{HERE}/dps48/L.sms")   # 48 x 16, rows = A-side forms
    R = parse_sms(f"{HERE}/dps48/R.sms")   # 48 x 16, rows = B-side forms
    P = parse_sms(f"{HERE}/dps48/P.sms")   # 16 x 48, cols = per product
    assert len(L) == 48 and len(L[0]) == 16
    assert len(R) == 48 and len(R[0]) == 16
    assert len(P) == 16 and len(P[0]) == 48
    if gauge:
        # projective gauge (alpha*beta*gamma = 1 per product): scale any
        # uniformly-scaled L/R row to +-1, compensating in P's column,
        # so the +-CSE model applies to both input sides verbatim.
        for M in (L, R):
            for i in range(48):
                mags = {abs(v) for v in M[i] if v}
                assert len(mags) == 1, f"mixed-magnitude row {i}"
                s = mags.pop()
                if s != 1:
                    M[i] = [v / s for v in M[i]]
                    for z in range(16):
                        P[z][i] *= s
    return L, R, P


def verify(L, R, P):
    """all 16^3 Brent equations over Q.  Determines the output-index
    convention (C row-major vs transposed) and proves the scheme."""
    n = 4
    for transpose_c in (False, True):
        ok = True
        for a in range(n):
            for b in range(n):
                x = n * a + b
                for c in range(n):
                    for d in range(n):
                        y = n * c + d
                        for p in range(n):
                            for q in range(n):
                                z = n * p + q if not transpose_c else n * q + p
                                s = sum(L[i][x] * R[i][y] * P[z][i]
                                        for i in range(R_PROD))
                                want = 1 if (b == c and a == p and d == q) else 0
                                if s != want:
                                    ok = False
                                    break
                            if not ok:
                                break
                        if not ok:
                            break
                    if not ok:
                        break
                if not ok:
                    break
            if not ok:
                break
        if ok:
            return "C^T (column-major)" if transpose_c else "C (row-major)"
    return None


# ---- CSE on the +-1 sides ----
def side_forms(M):
    """rows of a +-1 matrix as {var: +-1} dicts (skip zero entries)."""
    out = []
    for row in M:
        f = {}
        for j, v in enumerate(row):
            if v:
                assert v in (1, -1), f"non-unit entry {v}"
                f[j] = int(v)
        out.append(f)
    return out


def signed_perm(nvars, rng):
    """random signed permutation acting on the variable space."""
    perm = list(range(nvars))
    rng.shuffle(perm)
    sign = [rng.choice((1, -1)) for _ in range(nvars)]
    return perm, sign


def twist(forms, perm, sign):
    return [{perm[j]: v * sign[j] for j, v in f.items()} for f in forms]


def baseline():
    L, R, P = load()
    print("verify:", verify(L, R, P) or "FAILED")
    for name, M, publ in (("L", L, "104"), ("R", R, "84+1shift")):
        adds, _ = greedy_slp(side_forms(M))
        print(f"{name}: our deterministic greedy {adds} adds  "
              f"(published SLP: {publ})")


def transpose_forms(M):
    """columns of a +-1 matrix as forms over its row-index space."""
    rows, cols = len(M), len(M[0])
    out = []
    for j in range(cols):
        f = {}
        for i in range(rows):
            if M[i][j]:
                f[i] = int(M[i][j])
        out.append(f)
    return out


def storm(seconds, seed):
    L, R, P = load()
    # sanity for the transposition constant: no zero rows/columns
    for M in (L, R):
        assert all(any(row) for row in M)
        assert all(any(M[i][j] for i in range(48)) for j in range(16))
    sides = {
        "L":  side_forms(L),        # direct: 48 forms / 16 vars
        "R":  side_forms(R),
        "Lt": transpose_forms(L),   # transposed: 16 forms / 48 vars,
        "Rt": transpose_forms(R),   # SLP(L) = SLP(L^T) - 32
    }
    nv = {"L": 16, "R": 16, "Lt": 48, "Rt": 48}
    off = {"L": 0, "R": 0, "Lt": -32, "Rt": -32}
    rng = random.Random(seed)
    best = {"L": 10 ** 9, "R": 10 ** 9}
    t0 = time.time()
    n = 0
    while time.time() - t0 < seconds:
        n += 1
        for key, forms in sides.items():
            side = key[0]
            perm, sign = signed_perm(nv[key], rng)
            adds, _ = greedy_slp(twist(forms, perm, sign), rng)
            score = adds + off[key]
            if score < best[side]:
                best[side] = score
                print(f"[{n}] {side} {score}  (via {key})", flush=True)
    print(f"storm done: {n} rounds, best L {best['L']} (publ 104), "
          f"best R {best['R']} (publ 84+1)", flush=True)


if __name__ == "__main__":
    if sys.argv[1:2] == ["verify"]:
        L, R, P = load()
        v = verify(L, R, P)
        print("VERIFIED, output convention:" if v else "FAILED", v or "")
        sys.exit(0 if v else 1)
    elif sys.argv[1:2] == ["baseline"]:
        baseline()
    elif sys.argv[1:2] == ["storm"]:
        storm(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    else:
        print(__doc__)
