#!/usr/bin/env python3
"""Put Agarwal's replacement scheme (agarwal_replacement.py) into the coordinates of our
201 point, with the isotropy that lwh_transport.py finds for s(1/4) -> TARGET.

His scheme keeps 36 layers of s(2) and replaces the 12 layers F, G, U.  The same S3
element and X, Y, Z are applied to all 48 layers; the 36 kept layers go to their slots and
scalings under the found layer matching (so they coincide with the transported s(2)
point), and the 12 new layers take the slots of the layers they replace, each scaled by
powers of 2 so that its U and V factors have as many entries of absolute value 1 as
possible.  Writes OUTPREFIX_{L,R,P}.sms (Brent-checked) in our convention.

  agarwal_transport.py TEX TARGETPREFIX OUTPREFIX
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import agarwal_replacement as AR  # noqa: E402
import lwh_family as F  # noqa: E402
import lwh_transport as LT  # noqa: E402
import slp48check as C  # noqa: E402


def best_pow2(M):
    """power of 2 s maximizing the number of entries of M with |s x| = 1."""
    best, bs = -1, Fr(1)
    for e in range(-8, 9):
        s = Fr(2) ** e
        cnt = sum(1 for row in M for x in row if x and abs(s * x) == 1)
        if cnt > best:
            best, bs = cnt, s
    return bs


def main():
    tex, target, out = sys.argv[1], sys.argv[2], sys.argv[3]
    layers = F.parse(tex)
    Ut, Vt, Wt = F.read_lrp(target)
    Tg = (Ut, Vt, [LT.T(M) for M in Wt])
    vcT, pcT = LT.colors(Tg)
    S0 = F.scheme(layers, Fr(1, 4))
    found = None
    for name, S in LT.s3_variants(S0):
        vcS, pcS = LT.colors(S)
        for k, pi in enumerate(LT.isomorphisms(vcS, pcS, vcT, pcT)):
            g = LT.try_transport(S, Tg, pi)
            if g is not None:
                found = (name, pi, g)
                break
            if k >= 2000:
                break
        if found:
            break
    assert found, "no isotropy found"
    name, pi, g = found
    X, Y, Z, Xi, Yi, Zi, a, b = g
    print(f"isotropy found: S3 {name}")
    # Agarwal's scheme in the Li-Wang-Hu (cyclic) convention, layer by layer
    (U, V, W), (U2, V2, W2), (nU, nV, nW), _ = AR.build(tex)
    removed = sorted(set(AR.FG) | set(AR.GG) | set(AR.UG))
    keep = [k for k in range(1, 49) if k not in removed]
    # layer list: original index -> factors (kept), and the new ones
    lay = {k: (U[k - 1], V[k - 1], W[k - 1]) for k in keep}
    newl = list(zip(nU, nV, nW))

    def s3(tri):
        u, v, w = tri
        variants = dict(LT.s3_variants(([u], [v], [w])))
        uu, vv, ww = variants[name]
        return uu[0], vv[0], ww[0]

    outU, outV, outW = [None] * 48, [None] * 48, [None] * 48
    for k in keep:
        u, v, w = s3(lay[k])
        i = k - 1
        outU[pi[i]] = [[a[i] * x for x in row] for row in LT.mm(LT.mm(X, u), Yi)]
        outV[pi[i]] = [[b[i] * x for x in row] for row in LT.mm(LT.mm(Y, v), Zi)]
        outW[pi[i]] = [[x / (a[i] * b[i]) for x in row] for row in LT.mm(LT.mm(Z, w), Xi)]
    slots = [pi[k - 1] for k in removed]

    def cost(m, s):
        vals = [abs(s * x) for row in m for x in row if x]
        return sum(1 for x in vals if x != 1), max(vals) / min(vals) if vals else 1

    for slot, tri in zip(slots, newl):
        u, v, w = s3(tri)
        u = LT.mm(LT.mm(X, u), Yi)
        v = LT.mm(LT.mm(Y, v), Zi)
        w = LT.mm(LT.mm(Z, w), Xi)
        # powers of 2 for U and V (W gets the inverse product), chosen jointly: fewest
        # coefficients outside {0, +-1}, then the smallest largest entry
        best = None
        for ea in range(-10, 11):
            for eb in range(-10, 11):
                sa, sb = Fr(2) ** ea, Fr(2) ** eb
                n = cost(u, sa)[0] + cost(v, sb)[0] + cost(w, 1 / (sa * sb))[0]
                big = max(abs(x) for m, s in ((u, sa), (v, sb), (w, 1 / (sa * sb))) for row in m for x in row for x in [s * x])
                key = (n, big)
                if best is None or key < best[0]:
                    best = (key, sa, sb)
        _, sa, sb = best
        outU[slot] = [[sa * x for x in row] for row in u]
        outV[slot] = [[sb * x for x in row] for row in v]
        outW[slot] = [[x / (sa * sb) for x in row] for row in w]
    L, R, P = F.to_lrp(outU, outV, outW, True)
    bad = C.brent(L, R, P)
    print(f"transported Agarwal scheme: {4096 - bad}/4096 Brent equations hold")
    assert bad == 0
    for nm, M in (("L", L), ("R", R), ("P", P)):
        F.write_sms(f"{out}_{nm}.sms", M)
    vals = sorted({abs(x) for M in (L, R, P) for row in M for x in row if x})
    trip = {}
    for k in range(48):
        tr = (F.rank(outU[k]), F.rank(outV[k]), F.rank(outW[k]))
        trip[tr] = trip.get(tr, 0) + 1
    print(f"wrote {out}_{{L,R,P}}.sms; rank triples {trip}; |coefficients| {[str(v) for v in vals]}")


if __name__ == "__main__":
    main()
