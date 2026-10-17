#!/usr/bin/env python3
"""<4x4x4:r> mod-2 schemes: convert our .bits files to PLinOpt sms
triplets (and back), Brent-check, and print a class invariant.

Conventions.  Our .bits (matmul/anf.rs): r alpha blocks, then r beta
blocks, then r gamma blocks, 16 bits each, row-major (bit 4i+j = entry
(i,j)); sum_m alpha_m[a,b] beta_m[c,d] gamma_m[p,q] = [b=c][a=p][d=q], i.e.
product m = <U_m, A> <V_m, B> and C = sum_m product_m W_m with U = alpha,
V = beta, W = gamma.  PLinOpt: L row m = U_m, R row m = V_m, P column m
= W_m (row-major Vect, 1-based sms indices).

Invariant: the multiset of per-product rank triples (rank U, rank V,
rank W), minimized over the six slot permutations (the cyclic and
transpose symmetries permute the three ranks; GL actions keep them).

Usage:
  scheme47.py tosms SCHEME.bits OUTPREFIX
  scheme47.py tobits PREFIX OUT.bits
  scheme47.py info (SCHEME.bits | PREFIX) ...
"""
import itertools
import sys
from collections import Counter


def rank2(m):
    rows = [(m >> (4 * i)) & 0xF for i in range(4)]
    r = 0
    for c in range(4):
        piv = next((i for i in range(r, 4) if (rows[i] >> c) & 1), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(4):
            if i != r and (rows[i] >> c) & 1:
                rows[i] ^= rows[r]
        r += 1
    return r


def load_bits(path):
    s = open(path).read().strip()
    assert set(s) <= {"0", "1"} and len(s) % 48 == 0, f"{path}: not a 4x4x4 bits file"
    r = len(s) // 48
    blk = lambda off, m: sum(int(s[off + 16 * m + k]) << k for k in range(16))
    U = [blk(0, m) for m in range(r)]
    V = [blk(16 * r, m) for m in range(r)]
    W = [blk(32 * r, m) for m in range(r)]
    return U, V, W


def read_sms(path):
    with open(path) as f:
        rows, cols = map(int, f.readline().split()[:2])
        mask = [0] * rows
        for line in f:
            t = line.split()
            if len(t) < 3:
                continue
            i, j, v = map(int, t[:3])
            if i == 0 and j == 0:
                break
            if v % 2:
                mask[i - 1] ^= 1 << (j - 1)
    return rows, cols, mask


def load_sms(pre):
    _, _, U = read_sms(f"{pre}_L.sms")
    _, _, V = read_sms(f"{pre}_R.sms")
    rp, cp, P = read_sms(f"{pre}_P.sms")
    W = [sum(((P[p] >> k) & 1) << p for p in range(rp)) for k in range(cp)]
    return U, V, W


def load(arg):
    return load_bits(arg) if arg.endswith(".bits") else load_sms(arg)


def brent_ok(U, V, W):
    for a in range(16):
        for b in range(16):
            got = 0
            for u, v, w in zip(U, V, W):
                if (u >> a) & 1 and (v >> b) & 1:
                    got ^= w
            ai, aj, bi, bj = a // 4, a % 4, b // 4, b % 4
            if got != ((1 << (4 * ai + bj)) if aj == bi else 0):
                return False
    return True


def invariant(U, V, W):
    tri = [(rank2(u), rank2(v), rank2(w)) for u, v, w in zip(U, V, W)]
    return min(tuple(sorted(tuple(t[i] for i in p) for t in tri))
               for p in itertools.permutations(range(3)))


def write_sms(U, V, W, pre):
    r = len(U)
    for side, M in (("L", U), ("R", V)):
        lines = [f"{r} 16 M"]
        lines += [f"{i + 1} {j + 1} 1" for i, x in enumerate(M) for j in range(16) if (x >> j) & 1]
        open(f"{pre}_{side}.sms", "w").write("\n".join(lines + ["0 0 0"]) + "\n")
    lines = [f"16 {r} M"]
    lines += [f"{p + 1} {k + 1} 1" for p in range(16) for k, x in enumerate(W) if (x >> p) & 1]
    open(f"{pre}_P.sms", "w").write("\n".join(lines + ["0 0 0"]) + "\n")


def to_bits(U, V, W):
    return "".join("".join(str((x >> k) & 1) for k in range(16)) for M in (U, V, W) for x in M)


def main(a):
    if len(a) >= 2 and a[1] == "tosms" and len(a) == 4:
        U, V, W = load_bits(a[2])
        assert brent_ok(U, V, W), "Brent FAIL"
        write_sms(U, V, W, a[3])
        print(f"wrote {a[3]}_{{L,R,P}}.sms (rank {len(U)}, Brent OK)")
    elif len(a) >= 2 and a[1] == "tobits" and len(a) == 4:
        U, V, W = load_sms(a[2])
        assert brent_ok(U, V, W), "Brent FAIL"
        open(a[3], "w").write(to_bits(U, V, W) + "\n")
        print(f"wrote {a[3]} (rank {len(U)}, Brent OK)")
    elif len(a) >= 3 and a[1] == "info":
        for arg in a[2:]:
            U, V, W = load(arg)
            inv = invariant(U, V, W)
            ok = brent_ok(U, V, W)
            c = Counter(inv)
            print(f"{arg}: rank {len(U)}, Brent {'OK' if ok else 'FAIL'}, "
                  f"rank-triples {sorted(c.items())}")
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main(sys.argv)
