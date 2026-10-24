#!/usr/bin/env python3
"""The stabilizer of a <4x4x4:48> decomposition (A. Sedoglavic's question): every isotropy that
sends the decomposition to itself, permuting its 48 layers.  In lwh_transport's cyclic reading
an isotropy is a slot map sigma in S3 followed by (U, V, W) -> (X U Y^-1, Y V Z^-1, Z W X^-1)
with per-layer scalings; for each of the six sigma, every layer matching sigma(T) -> T allowed
by the isotropy invariants is tried, X, Y, Z are solved exactly and the image is checked to be T
layer by layer.  The map 'cyc2+rev' sends (U, V, W) to (V^T, U^T, W^T): its elements carry the
L factors onto the R factors.

Per element: the slot map, the cycle type of its permutation of the 48 layers, and whether X, Y,
Z are signed permutation matrices up to scale (then it permutes and negates matrix entries, and
a program for one leg maps to the others by relabelling).

  stabilizer48.py PREFIX        (PREFIX_{L,R,P}.sms in our convention)
"""
import os
import sys
from collections import Counter
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lwh_family as F  # noqa: E402
import lwh_transport as LT  # noqa: E402
import slp48check as C  # noqa: E402


def cycle_type(pi):
    seen, out = set(), []
    for k in range(48):
        if k in seen:
            continue
        n, j = 0, k
        while j not in seen:
            seen.add(j)
            j = pi[j]
            n += 1
        out.append(n)
    return tuple(sorted(out, reverse=True))


def monomial(M):
    """M is a signed permutation matrix up to one scalar"""
    nz = [abs(x) for row in M for x in row if x != 0]
    return (len(nz) == 4 and len(set(nz)) == 1
            and all(sum(1 for x in row if x) == 1 for row in M)
            and all(sum(1 for i in range(4) if M[i][j]) == 1 for j in range(4)))


def order_of(ct):
    from math import lcm
    o = 1
    for c in ct:
        o = lcm(o, c)
    return o


def main():
    prefix = sys.argv[1]
    U, V, W = F.read_lrp(prefix)
    Tg = (U, V, [LT.T(M) for M in W])
    assert C.brent(*F.to_lrp(*Tg, True)) == 0, "fails Brent in the cyclic reading"
    vcT, pcT = LT.colors(Tg)
    elems = []
    for name, S in LT.s3_variants(Tg):
        vcS, pcS = LT.colors(S)
        tried = ok = 0
        for pi in LT.isomorphisms(vcS, pcS, vcT, pcT):
            tried += 1
            g = LT.try_transport(S, Tg, pi)
            if g is None:
                continue
            img = LT.apply(g, S, pi)
            assert all(img[s][k] == Tg[s][k] for s in range(3) for k in range(48)), "image differs"
            X, Y, Z = g[0], g[1], g[2]
            elems.append((name, cycle_type(pi), all(monomial(M) for M in (X, Y, Z)), (X, Y, Z)))
            ok += 1
        print(f"  {name:9s}: {tried} layer matchings allowed by the invariants, {ok} isotropies")
    print(f"stabilizer of {os.path.basename(prefix)}: order {len(elems)}")
    by = Counter((e[0], order_of(e[1]), e[1], e[2]) for e in elems)
    print("  slot map  order  cycle type on the 48 layers             signed permutation?  count")
    for (name, o, ct, mono), n in sorted(by.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2])):
        cts = " ".join(f"{c}^{m}" for c, m in sorted(Counter(ct).items(), reverse=True))
        print(f"  {name:9s} {o:5d}  {cts:40s} {'yes' if mono else 'no ':3s}                 {n}")
    four = [e for e in elems if e[0] == "id" and order_of(e[1]) == 4 and e[2]]
    print(f"order-4 elements acting by signed permutation matrices with trivial slot map: {len(four)}")
    for name, ct, mono, (X, Y, Z) in four[:2]:
        for nm, M in (("X", X), ("Y", Y), ("Z", Z)):
            s = next(x for row in M for x in row if x)
            print(f"    {nm} = {[[int(x / s) for x in row] for row in M]}")
        print()
    lr = [e for e in elems if e[0] == "cyc2+rev"]
    print(f"elements carrying L onto R: {len(lr)}, of them by signed permutations: {sum(1 for e in lr if e[2])}")


if __name__ == "__main__":
    main()
