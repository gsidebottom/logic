#!/usr/bin/env python3
"""f3scan: whole-orbit lower bound over F_3 on the additions of 3x3 rank-23
schemes -- the mod-3 counterpart of the mod-2 bounds behind the 55 record.

Why F_3: a scheme over Z[1/2] reduces mod 3 (1/2 -> 2 = -1), and any
program for it reduces to an F_3 program with the same additions, its
scalings becoming free signs.  So the F_3 minimum over a class's orbit is a
lower bound on the additions (scalings not even counted) of every Z[1/2]
representative whose reduction lies in that orbit, i.e. every
representative reached from the scanned scheme by a basis change that is
invertible mod 3.  The mod-2 arguments say nothing about such schemes.

Model over F_3, negation free (so every nonzero scaling is free): the cost
of a leg is the number of additions x +- y that compute all 23 rows, up to
sign, from the 9 inputs.  Lower bound per leg: the number of distinct rows
up to sign that are not +-unit vectors, plus one when the closure of the
inputs under "add any target that is +-a +-b for available a, b" misses a
target (then some addition computes a non-target).  The output leg counts
transposed, +14 (transposition principle, 23 - 9).

Orbit: (P, Q, R) in GL(3,3)^3 acts by A -> P A Q^-1, B -> Q B R^-1,
C~ -> R C~ P^-1.  Each factor matters only through its LEFT coset of the
monomial matrices (P -> M P permutes and signs the rows of every P A Q^-1
and the columns of every R C~ P^-1 the same way for all 23 rows, which
leaves addition counts unchanged; likewise Q and R): 234 cosets, three
234x234 tables, min-plus over 234^3 triples.  Slot symmetries permute the
legs and leave the total unchanged, so one variant covers the de Groote
orbit.  A random-element gate checks the coset invariance.

Usage:
  f3scan.py one FILE [--target 54]           verbose single scheme (.tab or Hell's Bells .txt)
  f3scan.py db OUT_CSV [--jobs N] [--target 54]
  f3scan.py hb DATADIR VERDICTS_CSV OUT_CSV [--jobs N] [--target 54]
Resumable: names already in OUT_CSV are skipped.
"""
import glob
import os
import random
import sys
import tarfile
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np

M = os.path.dirname(os.path.abspath(__file__))
R23 = 23
N = 3 ** 9
W = np.array([3 ** k for k in range(9)], dtype=np.int64).reshape(3, 3)  # weight of entry (i, j) = 3^(3i+j)
TRITS = np.array([[(m // 3 ** k) % 3 for k in range(9)] for m in range(N)], dtype=np.int64).reshape(N, 3, 3)


def idx_of(mat):
    return int((np.asarray(mat, dtype=np.int64) % 3 * W).sum())


def det3(t):
    return int(round(np.linalg.det(t.astype(float)))) % 3


def inv3(m):
    t = TRITS[m]
    d = det3(t)
    assert d != 0
    adj = np.round(np.linalg.inv(t.astype(float)) * np.linalg.det(t.astype(float))).astype(np.int64) % 3
    inv = (adj * (1 if d == 1 else 2)) % 3  # 2^-1 = 2 in F_3
    assert ((t @ inv) % 3 == np.eye(3, dtype=np.int64)).all()
    return idx_of(inv)


def mul(a, b):
    return idx_of(TRITS[a] @ TRITS[b])


GL = [m for m in range(N) if det3(TRITS[m]) != 0]
MON = [m for m in GL if all(np.count_nonzero(TRITS[m][i]) == 1 for i in range(3)) and all(np.count_nonzero(TRITS[m][:, j]) == 1 for j in range(3))]
assert len(GL) == 11232 and len(MON) == 48
_rep = {}
for g in GL:
    if g not in _rep:
        coset = [mul(mu, g) for mu in MON]  # left coset: M g
        r = min(coset)
        for c in coset:
            _rep[c] = r
REPS = sorted(set(_rep.values()))
assert len(REPS) == 234
INV = {g: inv3(g) for g in REPS}
NR = len(REPS)
# LEFT[p][m] = index of REPS[p] * m ; RIGHTI[q][m] = index of m * REPS[q]^-1
LEFT = np.stack([((np.einsum("ij,njk->nik", TRITS[p], TRITS) % 3) * W).sum(axis=(1, 2)) for p in REPS])
RIGHTI = np.stack([((np.einsum("nij,jk->nik", TRITS, TRITS[INV[q]]) % 3) * W).sum(axis=(1, 2)) for q in REPS])
# per matrix index: 18-bit key (ones | twos << 9) normalized so the lowest nonzero coordinate is 1
ONES = np.array([sum(1 << k for k in range(9) if (m // 3 ** k) % 3 == 1) for m in range(N)], dtype=np.int64)
TWOS = np.array([sum(1 << k for k in range(9) if (m // 3 ** k) % 3 == 2) for m in range(N)], dtype=np.int64)
NZ = ONES | TWOS
LOW = NZ & -NZ
FLIP = (TWOS & LOW) != 0
KEY = np.where(FLIP, TWOS | (ONES << 9), ONES | (TWOS << 9))
KEY = np.where(NZ == 0, -1, KEY)  # zero rows cost nothing
KEY = np.where(np.array([bin(int(v)).count("1") == 1 for v in NZ]), -1, KEY)  # +-unit vectors are inputs
UNIT_KEYS = [1 << k for k in range(9)]


def f3_add(x, y):
    x1, x2, y1, y2 = x & 511, x >> 9, y & 511, y >> 9
    s1 = (x1 & ~y1 & ~y2) | (y1 & ~x1 & ~x2) | (x2 & y2)
    s2 = (x2 & ~y1 & ~y2) | (y2 & ~x1 & ~x2) | (x1 & y1)
    return (s1 & 511) | ((s2 & 511) << 9)


def f3_neg(x):
    return (x >> 9) | ((x & 511) << 9)


def f3_norm(x):
    nz = (x & 511) | (x >> 9)
    if nz == 0:
        return 0
    return f3_neg(x) if (x >> 9) & (nz & -nz) else x


def closure_misses(keys):
    """1 if the inputs' closure under 'add any target that is +-a +-b' misses a target."""
    rem = set(int(k) for k in keys if k >= 0)
    have = set(UNIT_KEYS)
    grew = True
    while rem and grew:
        grew = False
        for u in list(rem):
            hit = False
            for a in have:
                if f3_norm(f3_add(u, f3_neg(a))) in have or f3_norm(f3_add(u, a)) in have:
                    hit = True
                    break
            if hit:
                have.add(u)
                rem.discard(u)
                grew = True
    return 1 if rem else 0


def tcount_table(rows, left_is_P):
    """rows: 23 matrix indices of a leg.  Table T[i][j] = distinct non-unit
    targets of REPS[i] * row * REPS[j]^-1, and the (i, j, 23) key array."""
    L = LEFT[:, rows]  # (NR, 23)
    full = RIGHTI[:, L]  # (NR_j, NR_i, 23)
    full = full.transpose(1, 0, 2)  # (i, j, 23)
    keys = KEY[full]
    s = np.sort(keys, axis=2)
    distinct = (s[:, :, 1:] != s[:, :, :-1]).sum(axis=2) + 1
    t = distinct - (s[:, :, 0] == -1)
    return t.astype(np.int16), keys


def partner_min(tb, tc):
    """PM[q][p] = min_r tb[q][r] + tc[r][p]."""
    out = np.empty((NR, NR), dtype=np.int32)
    for q in range(NR):
        out[q] = (tb[q][:, None].astype(np.int32) + tc).min(axis=0)
    return out


def scan(legs, target=54, verbose=False):
    """legs: three lists of 23 matrix indices (A, B, C~ rows mod 3).
    Returns (bound_targets, bound_closure, n_triples_le_target, n_closures)."""
    goal = target - 14
    tA, kA = tcount_table(legs[0], True)   # [p][q]
    tB, kB = tcount_table(legs[1], True)   # [q][r]
    tC, kC = tcount_table(legs[2], True)   # [r][p]

    def totals(ta, tb, tc):
        best, cnt = 10 ** 9, 0
        pm = partner_min(tb, tc)  # [q][p]
        tot = ta.astype(np.int32) + pm.T  # [p][q] = ta[p][q] + min_r(...)
        return int(tot.min()), pm

    b1, pmA = totals(tA, tB, tC)
    if verbose:
        print(f"  target counts alone: orbit bound {b1 + 14}")
    if b1 > goal:
        return b1 + 14, b1 + 14, 0, 0
    # closure bits for entries that can still sit in a triple at or below the goal
    ta, tb, tc = tA.astype(np.int32), tB.astype(np.int32), tC.astype(np.int32)
    nclos = 0

    def refine(t, keys, need):  # need[i][j] = largest value of this entry still allowing the goal
        nonlocal nclos
        ii, jj = np.nonzero(t <= need)
        t2 = t.copy()
        for i, j in zip(ii, jj):
            t2[i, j] += closure_misses(keys[i, j])
            nclos += 1
        return t2

    pmA = partner_min(tb, tc)  # [q][p]
    ta2 = refine(ta, kA, goal - pmA.T)
    pmB = partner_min(tc, ta)  # [r][q]: min_p tc[r][p] + ta[p][q]
    tb2 = refine(tb, kB, goal - pmB.T)
    pmC = partner_min(ta, tb)  # [p][r]: min_q ta[p][q] + tb[q][r]
    tc2 = refine(tc, kC, goal - pmC.T)
    pm2 = partner_min(tb2, tc2)
    tot = ta2 + pm2.T
    b2 = int(tot.min())
    # count triples at or below the goal
    cnt = 0
    if b2 <= goal:
        for p in range(NR):
            m = ta2[p][:, None] + tb2 + tc2[:, p][None, :]
            cnt += int((m <= goal).sum())
    if verbose:
        print(f"  with closure bits ({nclos} closures): orbit bound {b2 + 14}, {cnt} coset triples <= {target}")
    return b1 + 14, b2 + 14, cnt, nclos


def gate(legs, rng):
    for _ in range(20):
        fam = rng.choice(legs)
        g, h, mu = rng.choice(GL), rng.choice(GL), rng.choice(MON)
        hinv = inv3(h)
        base = [mul(mul(g, m), hinv) for m in fam]
        v1 = [mul(mul(mul(mu, g), m), hinv) for m in fam]
        v2 = [mul(mul(g, m), inv3(mul(mu, h))) for m in fam]
        kb = KEY[base]
        for v in (v1, v2):
            kv = KEY[v]
            assert len(set(int(k) for k in kb if k >= 0)) == len(set(int(k) for k in kv if k >= 0)), "coset gate: target count"
            assert closure_misses(kb) == closure_misses(kv), "coset gate: closure bit"


# ---------------------------------------------------------------- inputs
def legs_from_signed(a_rows, b_rows, c_rows):
    """rows: 23 signed 9-tuples each (row-major 3x3); -> matrix indices mod 3."""
    def idx(v):
        return int(sum((int(x) % 3) * 3 ** k for k, x in enumerate(v)))
    return [[idx(v) for v in a_rows], [idx(v) for v in b_rows], [idx(v) for v in c_rows]]


def parse_tab(text):
    out, cur = [], []
    for ln in text.splitlines():
        if "|" not in ln:
            continue
        parts = [p.split() for p in ln.split("|")]
        if len(parts) != 3 or any(len(g) != 3 for g in parts):
            continue
        cur.append([[int(v) for v in g] for g in parts])
        if len(cur) == 3:
            out.append(tuple(tuple(v for r in cur for v in r[s]) for s in range(3)))
            cur = []
    return out if len(out) == R23 else None


def legs_from_tab(text):
    sm = parse_tab(text)
    if sm is None:
        return None
    return legs_from_signed([s[0] for s in sm], [s[1] for s in sm], [s[2] for s in sm])


def legs_from_hb(path):
    sys.path.insert(0, M + "/hb")
    import hbconvert
    alpha, beta, gamma = hbconvert.legs(hbconvert.parse(path), ("r", "r", "r"))
    # third leg is C~ = gamma transposed, the convention of the action formula
    return legs_from_signed([alpha[m].reshape(9) for m in range(R23)], [beta[m].reshape(9) for m in range(R23)], [gamma[m].T.reshape(9) for m in range(R23)])


def legs_from_slp(path):
    """Signed scheme from a program file in the style of
    external/i19-55adds-slp.txt: lines 'name = +-term +-term' over a11..a33,
    b11..b33, M1..M23 and wires; P_i, Q_i are the factors of M_i, C_pq the
    outputs.  Verifies C = AB on random integer matrices."""
    import re
    val = {}
    for ln in open(path):
        ln = ln.split("#")[0].strip()
        if "=" not in ln or "*" in ln:
            continue
        lhs, rhs = [x.strip() for x in ln.split("=", 1)]
        acc = {}
        toks = re.findall(r"[+-]|[A-Za-z]\w*|\d+", rhs)
        if toks == ["0"]:
            val[lhs] = {}
            continue
        op, i = 1, 0
        while i < len(toks):  # expression = term (op term)*, term = ['-'] name
            if toks[i] in "+-":
                op = -1 if toks[i] == "-" else 1
                i += 1
            unary = 1
            if toks[i] == "-":
                unary, i = -1, i + 1
            name = toks[i]
            i += 1
            for k, v in val.get(name, {name: 1}).items():
                acc[k] = acc.get(k, 0) + op * unary * v
            op = 1
        val[lhs] = {k: v for k, v in acc.items() if v}
    aidx = {f"a{r}{c}": 3 * (r - 1) + (c - 1) for r in range(1, 4) for c in range(1, 4)}
    bidx = {f"b{r}{c}": 3 * (r - 1) + (c - 1) for r in range(1, 4) for c in range(1, 4)}
    A = [[0] * 9 for _ in range(R23)]
    B = [[0] * 9 for _ in range(R23)]
    G = [[0] * 9 for _ in range(R23)]  # gamma[m][3p+q]
    for m in range(1, R23 + 1):
        for k, v in val[f"P{m}"].items():
            A[m - 1][aidx[k]] = v
        for k, v in val[f"Q{m}"].items():
            B[m - 1][bidx[k]] = v
    for pp in range(1, 4):
        for q in range(1, 4):
            for k, v in val[f"C{pp}{q}"].items():
                G[int(k[1:]) - 1][3 * (pp - 1) + (q - 1)] = v
    rng = random.Random(1)
    for _ in range(20):
        a = [rng.randint(-9, 9) for _ in range(9)]
        b = [rng.randint(-9, 9) for _ in range(9)]
        prod = [sum(A[m][i] * a[i] for i in range(9)) * sum(B[m][j] * b[j] for j in range(9)) for m in range(R23)]
        for pp in range(3):
            for q in range(3):
                got = sum(G[m][3 * pp + q] * prod[m] for m in range(R23))
                want = sum(a[3 * pp + k] * b[3 * k + q] for k in range(3))
                assert got == want, "SLP does not compute C = AB"
    Gt = [[G[m][3 * q + pp] for pp in range(3) for q in range(3)] for m in range(R23)]  # C~ = gamma transposed
    return legs_from_signed(A, B, Gt)


def work(item):
    name, legs, target = item
    t0 = time.time()
    b1, b2, cnt, ncl = scan(legs, target)
    if b2 == target + 1:
        # at the boundary the target-count bound may have been returned
        # unrefined: re-scan at target + 1 so the recorded bound is the
        # refined one and cnt counts the triples that could tie it
        _, b2, cnt, ncl2 = scan(legs, target + 1)
        ncl += ncl2
    return name, b1, b2, cnt, ncl, time.time() - t0


def run(items, out, jobs, target):
    done = set()
    if os.path.exists(out):
        done = {ln.split(",")[0] for ln in open(out) if not ln.startswith("name,")}
    else:
        open(out, "w").write("name,bound_targets,bound_closure,triples_le_target,closures,secs\n")
    items = [(n, l, target) for n, l in items if n not in done]
    print(f"{len(items)} schemes to scan ({len(done)} done); target {target}", flush=True)
    t0 = time.time()
    nlow = 0
    with ProcessPoolExecutor(max_workers=jobs) as ex:
        for i, (name, b1, b2, cnt, ncl, secs) in enumerate(ex.map(work, items, chunksize=2)):
            with open(out, "a") as f:
                f.write(f"{name},{b1},{b2},{cnt},{ncl},{secs:.1f}\n")
            if b2 <= target:
                nlow += 1
                print(f"*** {name}: F3 orbit bound {b2} <= {target} ({cnt} coset triples)", flush=True)
            if (i + 1) % 200 == 0:
                print(f"  {i + 1}/{len(items)} scanned, {nlow} at or below {target} ({time.time() - t0:.0f}s)", flush=True)
    print(f"done: {len(items)} scanned, {nlow} at or below {target} ({time.time() - t0:.0f}s)", flush=True)


def main():
    cmd = sys.argv[1]
    target = int(sys.argv[sys.argv.index("--target") + 1]) if "--target" in sys.argv else 54
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 8
    if cmd == "one":
        path = sys.argv[2]
        legs = legs_from_slp(path) if "slp" in os.path.basename(path) else legs_from_hb(path) if path.endswith(".txt") else legs_from_tab(open(path).read())
        gate(legs, random.Random(1))
        print("coset gate ok")
        t0 = time.time()
        b1, b2, cnt, ncl = scan(legs, target, verbose=True)
        print(f"F3 orbit lower bound on additions: {b2} ({ncl} closures, {time.time() - t0:.1f} s)")
    elif cmd == "db":
        out = sys.argv[2]
        tf = tarfile.open(f"{M}/dbcache/schemes.tgz", "r:gz")
        items = []
        for mem in tf:
            if mem.name.endswith(".tab"):
                legs = legs_from_tab(tf.extractfile(mem).read().decode())
                if legs is not None:
                    items.append((mem.name.rsplit("/", 1)[-1][:-4], legs))
        print(f"{len(items)} database schemes parsed", flush=True)
        gate(items[0][1], random.Random(3))
        print("coset gate ok", flush=True)
        run(items, out, jobs, target)
    elif cmd == "hb":
        datadir, verdicts, out = sys.argv[2:5]
        reps = {}
        for ln in open(verdicts):
            f = ln.rstrip("\n").split(",")
            if f[1] == "NEW" and f[2] not in reps:
                reps[f[2]] = f[0]
        items = [(cls, legs_from_hb(os.path.join(datadir, name + ".txt"))) for cls, name in sorted(reps.items())]
        gate(items[0][1], random.Random(5))
        print("coset gate ok", flush=True)
        run(items, out, jobs, target)
    elif cmd == "recheck":
        # re-scan the rows of a finished CSV whose bound equals target + 1 at target + 1
        src, csv_in, out = sys.argv[2], sys.argv[3], sys.argv[4]
        names = [ln.split(",")[0] for ln in open(csv_in) if not ln.startswith("name,") and int(ln.split(",")[2]) == target + 1]
        legs = {}
        if src == "db":
            want = set(names)
            tf = tarfile.open(f"{M}/dbcache/schemes.tgz", "r:gz")
            for mem in tf:
                nm = mem.name.rsplit("/", 1)[-1][:-4] if mem.name.endswith(".tab") else None
                if nm in want:
                    legs[nm] = legs_from_tab(tf.extractfile(mem).read().decode())
        else:  # src = Hell's Bells data dir; names are class ids -> rep file via the verdicts csv
            datadir, verdicts = src.split(":")
            rep = {}
            for ln in open(verdicts):
                f = ln.rstrip("\n").split(",")
                if f[1] == "NEW" and f[2] not in rep:
                    rep[f[2]] = f[0]
            for nm in names:
                legs[nm] = legs_from_hb(os.path.join(datadir, rep[nm] + ".txt"))
        with open(out, "w") as f:
            f.write("name,bound_refined,triples_at_bound,closures,secs\n")
            hist = {}
            for nm in names:
                t0 = time.time()
                _, b2, cnt, ncl = scan(legs[nm], target + 1)
                f.write(f"{nm},{b2},{cnt},{ncl},{time.time() - t0:.1f}\n")
                hist[(b2, cnt > 0)] = hist.get((b2, cnt > 0), 0) + 1
        print(f"rechecked {len(names)} rows at target {target + 1}: (refined bound, has triples at it) -> {dict(sorted(hist.items()))}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
