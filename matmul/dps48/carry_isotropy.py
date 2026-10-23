#!/usr/bin/env python3
"""Carry an isotropy found in one class over to another.

Given FROM and TO, two points of one orbit with the same product order (e.g. a transported
Li-Wang-Hu member and the orbit48 point annealed from it), find the isotropy g with
g . FROM = TO (basis changes X, Y, Z and per-product scalings; products matched in order,
or by invariants if that fails), and apply the same g to TARGET.  When TARGET has the same
output factor as FROM (all transported members share our record's P), g . TARGET has
exactly TO's output map, so TO's output program applies to it unchanged.

  carry_isotropy.py FROMPREFIX TOPREFIX TARGETPREFIX OUTPREFIX
(all PREFIX_{L,R,P}.sms; OUT is Brent-checked)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lwh_family as F  # noqa: E402
import lwh_transport as LT  # noqa: E402
import slp48check as C  # noqa: E402


def cyclic(prefix):
    U, V, W = F.read_lrp(prefix)
    return (U, V, [LT.T(M) for M in W])


def main():
    src, dst, tgt, out = sys.argv[1:5]
    S, D, T = cyclic(src), cyclic(dst), cyclic(tgt)
    for D_ in (S, D, T):
        assert C.brent(*F.to_lrp(*D_, True)) == 0
    g = LT.try_transport(S, D, list(range(48)))
    pi = list(range(48))
    if g is None:
        vcS, pcS = LT.colors(S)
        vcD, pcD = LT.colors(D)
        for k, p in enumerate(LT.isomorphisms(vcS, pcS, vcD, pcD)):
            g = LT.try_transport(S, D, p)
            if g is not None:
                pi = p
                break
            if k >= 2000:
                break
    assert g is not None, "no isotropy FROM -> TO found"
    print(f"isotropy FROM -> TO found ({'products in order' if pi == list(range(48)) else 'products permuted'})")
    img = LT.apply(g, T, pi)
    L, R, P = F.to_lrp(*img, True)
    bad = C.brent(L, R, P)
    print(f"g . TARGET: {4096 - bad}/4096 Brent equations hold")
    assert bad == 0
    same_out = sum(img[2][k] == D[2][k] for k in range(48))
    print(f"output factors equal to TO's: {same_out}/48")
    for nm, M in (("L", L), ("R", R), ("P", P)):
        F.write_sms(f"{out}_{nm}.sms", M)
    print(f"wrote {out}_{{L,R,P}}.sms")


if __name__ == "__main__":
    main()
