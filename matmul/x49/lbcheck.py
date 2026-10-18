#!/usr/bin/env python3
"""Independent check of `xor47 lbscan`: no point in the orbit of a rank-r
<4,4,4> scheme over F2 costs fewer than TARGET XORs.

Cost of a scheme = c(U) + c(V) + c(W) + (r - 16), where c(F) is the fewest
2-input XORs computing the vectors of family F from the 16 inputs (the W
side counted transposed).  Lower bound per side: the number of distinct
non-unit targets, plus one when the inputs' closure (repeatedly add any
target that is the XOR of two available signals) misses a target, since
then some gate must compute a non-target.  Side costs depend only on the
right cosets of the permutation matrices, so three 840x840 tables cover
the GL(4,2)^3 orbit, and the slot symmetries only permute coset triples.

Written separately from xor47.rs: its own GL(4,2) and coset enumeration,
numpy lookup tables for the action, a pure-Python closure.  Also checks
that the action formulas give Brent-valid schemes (with a negative
control) and that random orbit points match the tables of their cosets.

Usage: lbcheck.py PREFIX TARGET      (reads PREFIX_{L,R,P}.sms)
"""
import random
import sys

import numpy as np

NIN = 16


def read_rows(path):
    with open(path) as f:
        r, c = map(int, f.readline().split()[:2])
        rows = [0] * r
        for line in f:
            p = line.split()
            if len(p) < 3:
                continue
            i, j = int(p[0]), int(p[1])
            if i == 0 and j == 0:
                break
            if int(p[2]) % 2:
                rows[i - 1] ^= 1 << (j - 1)
    return r, c, rows


def load(pre):
    _, _, u = read_rows(pre + "_L.sms")
    _, _, v = read_rows(pre + "_R.sms")
    rp, cp, p = read_rows(pre + "_P.sms")
    assert rp == NIN and cp == len(u) == len(v)
    w = [sum(((p[c] >> k) & 1) << c for c in range(rp)) for k in range(cp)]
    return u, v, w


def bit(a, i, j):
    return (a >> (4 * i + j)) & 1


def mul(a, b):
    out = 0
    for i in range(4):
        for j in range(4):
            if sum(bit(a, i, k) & bit(b, k, j) for k in range(4)) & 1:
                out |= 1 << (4 * i + j)
    return out


def tr(a):
    return sum(bit(a, i, j) << (4 * j + i) for i in range(4) for j in range(4))


def inv(a):
    """Gauss-Jordan on [a | I]; None if singular."""
    rows = [(((a >> (4 * i)) & 0xF) | (1 << (4 + i))) for i in range(4)]
    for col in range(4):
        piv = next((r for r in range(col, 4) if (rows[r] >> col) & 1), None)
        if piv is None:
            return None
        rows[col], rows[piv] = rows[piv], rows[col]
        for r in range(4):
            if r != col and (rows[r] >> col) & 1:
                rows[r] ^= rows[col]
    return sum(((rows[i] >> 4) & 0xF) << (4 * i) for i in range(4))


def brent(u, v, w):
    for a in range(NIN):
        for b in range(NIN):
            got = 0
            for uk, vk, wk in zip(u, v, w):
                if (uk >> a) & 1 and (vk >> b) & 1:
                    got ^= wk
            ai, aj, bi, bj = a // 4, a % 4, b // 4, b % 4
            if got != ((1 << (4 * ai + bj)) if aj == bi else 0):
                return False
    return True


def act(s, x, y, z):
    """U' = X^T U Y^-T, V' = Y^T V Z^-T, W' = X^-1 W Z."""
    u, v, w = s
    xt, yt, yit, zit, xi = tr(x), tr(y), tr(inv(y)), tr(inv(z)), inv(x)
    return ([mul(mul(xt, m), yit) for m in u], [mul(mul(yt, m), zit) for m in v], [mul(mul(xi, m), z) for m in w])


def floor_of(fam):
    return len({m for m in fam if bin(m).count("1") > 1})


def closure_misses(fam):
    """1 if the inputs' closure does not reach every non-unit target."""
    rem = {m for m in fam if bin(m).count("1") > 1}
    have = {1 << i for i in range(NIN)}
    grew = True
    while rem and grew:
        grew = False
        for t in list(rem):
            if any((t ^ c) in have for c in have):
                have.add(t)
                rem.discard(t)
                grew = True
    return 1 if rem else 0


ALL = np.arange(1 << NIN, dtype=np.uint32)
ROWS = [(ALL >> (4 * k)) & 0xF for k in range(4)]
POP = np.array([bin(i).count("1") for i in range(1 << NIN)], dtype=np.uint8)


def left_lut(a):
    """a * M for every 4x4 matrix M."""
    out = np.zeros(1 << NIN, dtype=np.uint32)
    for i in range(4):
        row = np.zeros(1 << NIN, dtype=np.uint32)
        for k in range(4):
            if bit(a, i, k):
                row ^= ROWS[k]
        out |= row << (4 * i)
    return out


def right_lut(b):
    """M * b for every 4x4 matrix M."""
    brow = [(b >> (4 * k)) & 0xF for k in range(4)]
    out = np.zeros(1 << NIN, dtype=np.uint32)
    for i in range(4):
        row = np.zeros(1 << NIN, dtype=np.uint32)
        for k in range(4):
            row ^= ((ALL >> (4 * i + k)) & 1) * brow[k]
        out |= row << (4 * i)
    return out


def floors(t):
    """t: (..., r) target values; distinct non-unit count along the last axis."""
    s = np.sort(t, axis=-1)
    new = np.ones(s.shape, dtype=bool)
    new[..., 1:] = s[..., 1:] != s[..., :-1]
    return (new & (POP[s] > 1)).sum(axis=-1).astype(np.int16)


def main():
    pre, target = sys.argv[1], int(sys.argv[2])
    s0 = load(pre)
    r = len(s0[0])
    goal = target - (r - NIN)
    assert brent(*s0), "input scheme fails Brent"
    gl = [a for a in range(1 << NIN) if inv(a) is not None]
    perms = [a for a in gl if all(bin((a >> (4 * i)) & 0xF).count("1") == 1 for i in range(4)) and bin(a).count("1") == 4]
    assert len(gl) == 20160 and len(perms) == 24
    rep_of = {}
    for a in gl:
        if a not in rep_of:
            coset = [mul(a, q) for q in perms]
            m = min(coset)
            for c in coset:
                rep_of[c] = m
    reps = sorted(set(rep_of.values()))
    n = len(reps)
    assert n == 840
    idx = {a: i for i, a in enumerate(reps)}
    print(f"rank {r}; |GL(4,2)| = {len(gl)}, {n} cosets; side-sum goal {goal}")

    rng = random.Random(1)
    # the action formulas give valid schemes; a wrong formula does not
    for _ in range(12):
        x, y, z = rng.choice(gl), rng.choice(gl), rng.choice(gl)
        assert brent(*act(s0, x, y, z)), "action breaks Brent"
    bad = 0
    for _ in range(12):
        x, y, z = rng.choice(gl), rng.choice(gl), rng.choice(gl)
        u, v, w = s0
        bad += not brent([mul(mul(x, m), y) for m in u], v, w)
    assert bad >= 10, "negative control passed Brent too often"
    print("action check: 12/12 random orbit points pass Brent; wrong formula fails", bad, "/ 12")

    # floor tables, laid out U[x][y], V[y][z], W[z][x]
    u, v, w = (np.array(f, dtype=np.uint32) for f in s0)
    tabs = []
    for name, fam in (("U", u), ("V", v)):
        part = np.stack([left_lut(tr(a))[fam] for a in reps])  # (840 first, r)
        tab = np.zeros((n, n), dtype=np.int16)
        for j, b in enumerate(reps):
            tab[:, j] = floors(right_lut(tr(inv(b)))[part])
        tabs.append(tab)
        print(f"  {name} table: floors {tab.min()}..{tab.max()}")
    part = np.stack([left_lut(inv(b))[w] for b in reps])  # (840 second = X, r)
    tab = np.zeros((n, n), dtype=np.int16)
    for i, a in enumerate(reps):
        tab[i, :] = floors(right_lut(a)[part])
    tabs.append(tab)
    print(f"  W table: floors {tab.min()}..{tab.max()}")
    fu, fv, fw = tabs

    # random orbit points (any group elements) match the tables of their cosets
    for _ in range(40):
        x, y, z = rng.choice(gl), rng.choice(gl), rng.choice(gl)
        su, sv, sw = act(s0, x, y, z)
        xi, yi, zi = idx[rep_of[x]], idx[rep_of[y]], idx[rep_of[z]]
        assert (floor_of(su), floor_of(sv), floor_of(sw)) == (fu[xi, yi], fv[yi, zi], fw[zi, xi]), "coset table mismatch"
    print("coset check: 40/40 random orbit points match their coset entries")

    # triples whose floors alone allow the goal or less
    cand = []
    for x in range(n):
        tot = fu[x][:, None] + fv + fw[:, x][None, :]  # [y][z]
        ys, zs = np.nonzero(tot <= goal)
        cand.extend((x, int(y), int(z), int(tot[y, z])) for y, z in zip(ys, zs))
    print(f"{len(cand)} coset triples have floor sum <= {goal}")

    # closure bits for the sides of those triples
    def fam_at(side, i, j):
        a, b = reps[i], reps[j]
        if side == 0:
            return [mul(mul(tr(a), m), tr(inv(b))) for m in s0[0]]
        if side == 1:
            return [mul(mul(tr(a), m), tr(inv(b))) for m in s0[1]]
        return [mul(mul(inv(b), m), a) for m in s0[2]]

    bits = {}
    for x, y, z, _ in cand:
        for key in ((0, x, y), (1, y, z), (2, z, x)):
            if key not in bits:
                fam = fam_at(*key)
                assert floor_of(fam) == tabs[key[0]][key[1], key[2]]
                bits[key] = closure_misses(fam)
    below = at_goal = 0
    for x, y, z, f in cand:
        lb = f + bits[(0, x, y)] + bits[(1, y, z)] + bits[(2, z, x)]
        below += lb < goal
        at_goal += lb == goal
    print(f"closure bits computed for {len(bits)} sides; triples with lower bound < {goal}: {below}, = {goal}: {at_goal}")
    if below == 0:
        print(f"VERIFIED: every point of the orbit costs at least {target} ({at_goal} coset triples meet the bound)")
    else:
        print(f"NOT VERIFIED: {below} coset triples have lower bounds below {goal}")
        sys.exit(1)


if __name__ == "__main__":
    main()
