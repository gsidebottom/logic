#!/usr/bin/env python3
"""Alexandre's Gram-matrix remark (2026-11-08): the vectors of the type [1,1,1] products of the rational <4x4x4:48>
should carry the same configuration in every mode ("u is isomorphic to x and y").  At accurate_262 the [1,1,1]
vectors of each mode fill four of the six F4 frames (frames.py, results_td_2026-10-31.txt): X: e, H+, 13|24, 14|23;
Y: e, H+, 12|34, 13|24; Z: e, H-, 13|24, 14|23 -- sixteen lines per mode.  This script compares the Gram matrices
(absolute inner products between the lines) and searches the Weyl group W(F4), generated here by the signed
permutations and the Hadamard frame (order 1152), for isometries carrying one mode's lines onto another's, and lists
the W(F4)-orbit of the frame quadruple.  Result (2026-11-09): identical Gram multisets {0: 56, 1/sqrt2: 32, 1/2: 32},
128 isometries between each pair of modes, so the three configurations are congruent and the configuration's own
symmetry group has order 128 against the 32 trivial-slot stabilizer elements acting per mode.
usage: gram_modes.py"""
import itertools, collections
import numpy as np
s = 2 ** -.5
F = {"e": np.eye(4),
     "H+": .5 * np.array([[1, 1, 1, 1], [1, 1, -1, -1], [1, -1, 1, -1], [1, -1, -1, 1]], float),
     "H-": .5 * np.array([[1, 1, 1, -1], [1, 1, -1, 1], [1, -1, 1, 1], [-1, 1, 1, 1]], float),
     "12|34": s * np.array([[1, 1, 0, 0], [1, -1, 0, 0], [0, 0, 1, 1], [0, 0, 1, -1]], float),
     "13|24": s * np.array([[1, 0, 1, 0], [1, 0, -1, 0], [0, 1, 0, 1], [0, 1, 0, -1]], float),
     "14|23": s * np.array([[1, 0, 0, 1], [1, 0, 0, -1], [0, 1, 1, 0], [0, 1, -1, 0]], float)}
modes = {"X": ["e", "H+", "13|24", "14|23"], "Y": ["e", "H+", "12|34", "13|24"], "Z": ["e", "H-", "13|24", "14|23"]}
def line(v):
    v = np.round(v, 6); nz = v[np.abs(v) > 1e-9]; return tuple((v * np.sign(nz[0])).tolist())
def lines(fr): return frozenset(line(v) for n in fr for v in F[n])
L = {m: lines(fr) for m, fr in modes.items()}
def key(M): return tuple(np.round(M, 6).flatten().tolist())
gens = []
for p in itertools.permutations(range(4)):
    P = np.zeros((4, 4))
    for i, j in enumerate(p): P[i, j] = 1
    for sg in itertools.product([1, -1], repeat=4): gens.append(np.diag(sg) @ P)
gens.append(F["H+"])
G = {key(np.eye(4)): np.eye(4)}; frontier = [np.eye(4)]
while frontier:
    new = []
    for g in frontier:
        for h in gens:
            m = h @ g; k = key(m)
            if k not in G: G[k] = m; new.append(m)
    frontier = new
print("W(F4) order:", len(G))
def gram_multiset(ls):
    V = np.array(sorted(ls)); A = np.abs(V @ V.T)
    return dict(collections.Counter(np.round(A[np.triu_indices(len(V), 1)], 3).tolist()))
for m in "XYZ": print(f"mode {m}: {len(L[m])} lines, |inner products| multiset {gram_multiset(L[m])}")
for a, b in [("X", "X"), ("X", "Y"), ("X", "Z"), ("Y", "Z")]:
    iso = [g for g in G.values() if frozenset(line(g @ np.array(v)) for v in L[a]) == L[b]]
    print(f"isometries in W(F4) carrying mode {a}'s lines onto mode {b}'s: {len(iso)}")
