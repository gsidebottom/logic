#!/usr/bin/env python3
"""Every isotropy from one rank-48 point to another, exact, for Sedoglavic's lost isotropy from the original
rational <4x4x4:48|315> to accurate_262.  Each is written the way RFC 2610 writes them: a map on [L; R; P]
(s3_lrp.py), then (U x V x W) of Lemma 2.1 acting after it, with U, V, W primitive integer matrices.  The
transport itself is stabilizer48.py's; only the source differs.  Every element is checked layer by layer.

  iso_between.py SRC_PREFIX TGT_PREFIX OUT.json
"""
import json, math, os, sys
from fractions import Fraction as Fr
D = '/Users/greg/projects/logic/matmul/dps48'; sys.path.insert(0, D)
import stabilizer48 as S4
import lwh_family as F, lwh_transport as LT, slp48check as C

# lwh_transport's slot names against the maps of s3_lrp.py
ACT = {"id": "[L; R; P]", "cyc": "[R; P^T K; K L^T]", "cyc2": "[P^T K; L; K R^T]",
       "id+rev": "[P^T; R K; L^T]", "cyc+rev": "[L K; P^T; R^T]", "cyc2+rev": "[R K; L K; K P]"}

def prim(M):
    "M scaled to a primitive integer matrix with a positive first nonzero entry"
    den = math.lcm(*[x.denominator for r in M for x in r])
    I = [[int(x * den) for x in r] for r in M]
    g = math.gcd(*[x for r in I for x in r])
    s = next(x for r in I for x in r if x)
    g = g if s > 0 else -g
    return [[x // g for x in r] for r in I]

def point(prefix):
    U, V, W = F.read_lrp(prefix)
    return U, V, [LT.T(M) for M in W]

src, tgt, out = sys.argv[1:4]
S0, Tg = point(src), point(tgt)
for P in (S0, Tg):
    assert C.brent(*F.to_lrp(*P, True)) == 0
vcT, pcT = LT.colors(Tg)
el = []
for name, S in LT.s3_variants(S0):
    vcS, pcS = LT.colors(S)
    tried = ok = 0
    for pi in LT.isomorphisms(vcS, pcS, vcT, pcT):
        tried += 1
        g = LT.try_transport(S, Tg, pi)
        if g is None:
            continue
        img = LT.apply(g, S, pi)
        assert all(img[s][k] == Tg[s][k] for s in range(3) for k in range(48))
        X, Y, Z = g[0], g[1], g[2]
        # (X A Y^-1, Y B Z^-1, Z C X^-1) is Lemma 2.1's (U^-T A V^T, V^-T B W^T, W^-T C U^T) with U = X^-T etc.
        U, V, W = (prim(LT.T(LT.inv(M))) for M in (X, Y, Z))
        ok += 1
        el.append(dict(slot=name, act=ACT[name], pi=[pi[k] for k in range(48)], ct=list(S4.cycle_type(pi)), U=U, V=V, W=W,
                       mono=[S4.monomial(M) for M in (X, Y, Z)],
                       X=[[str(x) for x in r] for r in X], Y=[[str(x) for x in r] for r in Y], Z=[[str(x) for x in r] for r in Z]))
    print(f"{name:9s} {ACT[name]:20s} {tried} matchings allowed, {ok} isotropies", flush=True)
json.dump(el, open(out, 'w'))
print(f"{os.path.basename(src)} -> {os.path.basename(tgt)}: {len(el)} isotropies")
