#!/usr/bin/env python3
"""Mixed-inner Strassen schemes for <4,4,4> rank 49 over F2.

Outer: a 2x2 rank-7 scheme on 2x2 blocks; inner: for each outer product k
its own 2x2 rank-7 scheme I_k from Strassen's orbit (GL(2,2)^3 sandwich +
slot symmetries).  Product (k, j) = (U_k (x) u_j, V_k (x) v_j, W_k (x) w_j)
(Kronecker, block index outer: entry (2p+i, 2q+j)).  Every choice is a
valid scheme over any ring once the 2x2 schemes are lifted (Strassen's
orbit lifts), and the tensor square is the uniform choice.

Usage: mixed.py orbit                      (count inner schemes)
       mixed.py random N OUTDIR [SEED]     (N random mixed schemes as .bits)
"""
import itertools
import random
import sys

STRASSEN = ("100100111000000111001010010110011000010110100001110000111001001101011010110000011000")


def m2mul(a, b):
    out = 0
    for i in range(2):
        r = 0
        for j in range(2):
            if (a >> (2 * i + j)) & 1:
                r ^= (b >> (2 * j)) & 3
        out |= r << (2 * i)
    return out


def m2t(a):
    return sum(((a >> (2 * i + j)) & 1) << (2 * j + i) for i in range(2) for j in range(2))


GL2 = [(a, b) for a in range(16) for b in range(16) if m2mul(a, b) == 0b1001]


def strassen():
    s = [int(c) for c in STRASSEN]
    r = 7
    blk = lambda off, m: sum(s[off + 4 * m + k] << k for k in range(4))
    return [(blk(0, m), blk(4 * r, m), blk(8 * r, m)) for m in range(r)]


def sym(S, k):
    T = m2t
    return [[(u, v, w), (v, T(w), T(u)), (T(w), u, T(v)), (T(v), T(u), T(w)),
             (w, T(v), u), (T(u), w, v)][k] for (u, v, w) in S]


def act(S, x, y, z):
    return [(m2mul(m2mul(m2t(x[0]), u), m2t(y[1])), m2mul(m2mul(m2t(y[0]), v), m2t(z[1])),
             m2mul(m2mul(x[1], w), z[0])) for (u, v, w) in S]


def orbit():
    seen = {}
    base = strassen()
    for k in range(6):
        S = sym(base, k)
        for x, y, z in itertools.product(GL2, repeat=3):
            key = frozenset(act(S, x, y, z))
            seen.setdefault(key, sorted(key))
    return list(seen.values())


def kron(M, m):
    out = 0
    for p in range(2):
        for q in range(2):
            if (M >> (2 * p + q)) & 1:
                for i in range(2):
                    for j in range(2):
                        if (m >> (2 * i + j)) & 1:
                            out |= 1 << (4 * (2 * p + i) + (2 * q + j))
    return out


def mixed(outer, inners):
    prods = []
    for (U, V, W), inner in zip(outer, inners):
        for (u, v, w) in inner:
            prods.append((kron(U, u), kron(V, v), kron(W, w)))
    return prods


def to_bits(prods):
    U, V, W = zip(*prods)
    return "".join("".join(str((x >> k) & 1) for k in range(16)) for M in (U, V, W) for x in M)


if __name__ == "__main__":
    sys.path.insert(0, __file__.rsplit("/", 2)[0] + "/x47")
    from scheme47 import brent_ok
    orb = orbit()
    if sys.argv[1] == "orbit":
        print(f"{len(orb)} distinct 2x2 rank-7 schemes in Strassen's F2 orbit")
        S = strassen()
        P = mixed(S, [S] * 7)
        print("tensor square valid:", brent_ok(*zip(*P)))
    elif sys.argv[1] == "random":
        n, outdir = int(sys.argv[2]), sys.argv[3]
        rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
        import os
        os.makedirs(outdir, exist_ok=True)
        for t in range(n):
            outer = rng.choice(orb)
            inners = [rng.choice(orb) for _ in range(7)]
            P = mixed(outer, inners)
            assert brent_ok(*zip(*P)), "mixed scheme fails Brent"
            open(f"{outdir}/mix-{t:05d}.bits", "w").write(to_bits(P) + "\n")
        print(f"wrote {n} mixed schemes to {outdir} (all Brent-valid)")
