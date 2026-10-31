#!/usr/bin/env python3
"""The stabilizer of a rank-48 point with its matrices, as stabilizer48.py finds it, for the question
in Sedoglavic's reply: at which points does the whole stabilizer act by signed permutations, and is it
orthogonal at the gamma_2 minimum?  Writes every element to OUT.json as exact fractions.

  stab_matrices.py PREFIX OUT.json
"""
import json, os, sys
from collections import Counter
from fractions import Fraction as Fr
D = '/Users/greg/projects/logic/matmul/dps48'; sys.path.insert(0, D)
import stabilizer48 as S4
import lwh_family as F, lwh_transport as LT, slp48check as C

def scaled_orth(M):
    "M M^T is a scalar matrix"
    P = [[sum(M[i][k] * M[j][k] for k in range(4)) for j in range(4)] for i in range(4)]
    return all(P[i][j] == 0 for i in range(4) for j in range(4) if i != j) and len({P[i][i] for i in range(4)}) == 1

prefix, out = sys.argv[1:3]
U, V, W = F.read_lrp(prefix)
Tg = (U, V, [LT.T(M) for M in W])
assert C.brent(*F.to_lrp(*Tg, True)) == 0
vcT, pcT = LT.colors(Tg)
el = []
for name, S in LT.s3_variants(Tg):
    vcS, pcS = LT.colors(S)
    for pi in LT.isomorphisms(vcS, pcS, vcT, pcT):
        g = LT.try_transport(S, Tg, pi)
        if g is None: continue
        img = LT.apply(g, S, pi)
        assert all(img[s][k] == Tg[s][k] for s in range(3) for k in range(48))
        X, Y, Z = g[0], g[1], g[2]
        el.append(dict(slot=name, pi=[pi[k] for k in range(48)], ct=list(S4.cycle_type(pi)),
                       mono=[S4.monomial(M) for M in (X, Y, Z)], orth=[scaled_orth(M) for M in (X, Y, Z)],
                       X=[[str(x) for x in r] for r in X], Y=[[str(x) for x in r] for r in Y], Z=[[str(x) for x in r] for r in Z]))
json.dump(el, open(out, 'w'))
print(f"{os.path.basename(prefix)}: stabilizer order {len(el)}, slot maps {dict(Counter(e['slot'] for e in el))}")
print(f"   all three matrices signed permutations: {sum(all(e['mono']) for e in el)};  all three orthogonal up to scale: {sum(all(e['orth']) for e in el)}")
for i, n in enumerate("XYZ"):
    print(f"   {n}: signed permutation in {sum(e['mono'][i] for e in el)}, orthogonal up to scale in {sum(e['orth'][i] for e in el)}")
