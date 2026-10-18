#!/usr/bin/env python3
"""Pairwise class invariant for <4,4,4> schemes over F2: the multiset of
(rank(U_i+U_j), rank(V_i+V_j), rank(W_i+W_j)) over product pairs,
minimized over the six slot permutations (GL actions keep ranks; the
cyclic/transpose symmetries permute the three slots).  Different values
=> inequivalent schemes; equal values are evidence, not proof.
Usage: pairinv.py SCHEME(.bits|PREFIX) ..."""
import itertools
import sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 2)[0] + "/x47")
from scheme47 import load, rank2


def pairinv(U, V, W):
    tri = [(rank2(U[i] ^ U[j]), rank2(V[i] ^ V[j]), rank2(W[i] ^ W[j]))
           for i in range(len(U)) for j in range(i + 1, len(U))]
    return min(tuple(sorted(Counter(tuple(t[k] for k in p) for t in tri).items()))
               for p in itertools.permutations(range(3)))


if __name__ == "__main__":
    seen = {}
    for a in sys.argv[1:]:
        inv = pairinv(*load(a))
        h = hash(inv) & 0xFFFFFF
        seen.setdefault(inv, []).append(a)
        print(f"{a}: pair-invariant #{h:06x}")
    print(f"{len(seen)} distinct pair-invariants over {len(sys.argv) - 1} schemes")
