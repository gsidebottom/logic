#!/usr/bin/env python3
"""The six orthonormal frames of the F4 root system at the gamma_2 minimum (accurate_262): which of them
carry the [1,1,1] vectors, how primal and dual vectors divide into mutually unbiased bases, and in which
frames the stabilizer acts by signed permutations.  Frame matrices have the frame vectors as rows.  In the
cyclic reading, a triple of frames (A, B, C) gives the point (A U B^T, B V C^T, C W A^T), with
id-slot elements X' = A X A^T, Y' = B Y B^T, Z' = C Z C^T and slot elements X' = A X C^T, Y' = B Y B^T,
Z' = C Z A^T.

  frames.py PREFIX STAB.json
"""
import itertools, json, sys
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
sys.path.insert(0, '/Users/greg/projects/logic/matmul/dps48/rfc2610')
from fractions import Fraction as Fr
from collections import Counter
import numpy as np
import gamma_fixed as GF
s = 2 ** -.5
E = np.eye(4)
Fr_ = {"e": E,
       "H+": .5 * np.array([[1, 1, 1, 1], [1, 1, -1, -1], [1, -1, 1, -1], [1, -1, -1, 1]], float),
       "H-": .5 * np.array([[1, 1, 1, -1], [1, 1, -1, 1], [1, -1, 1, 1], [-1, 1, 1, 1]], float),
       "12|34": s * np.array([[1, 1, 0, 0], [1, -1, 0, 0], [0, 0, 1, 1], [0, 0, 1, -1]], float),
       "13|24": s * np.array([[1, 0, 1, 0], [1, 0, -1, 0], [0, 1, 0, 1], [0, 1, 0, -1]], float),
       "14|23": s * np.array([[1, 0, 0, 1], [1, 0, 0, -1], [0, 1, 1, 0], [0, 1, -1, 0]], float)}
line = lambda x: tuple(np.round(x * np.sign(x[np.abs(x) > 1e-9][0]), 6).tolist())
of = {line(v): n for n, F in Fr_.items() for v in F}
assert len(of) == 24
pre, st = sys.argv[1:3]
U, V, W = GF.load(pre); el = json.load(open(st))
M = lambda m: np.array([[float(Fr(x)) for x in r] for r in m])
rk1 = lambda A: np.linalg.matrix_rank(A, tol=1e-9) == 1
idx = [k for k in range(48) if rk1(U[k]) and rk1(V[k]) and rk1(W[k])]
def lv(A):
    a, _, b = np.linalg.svd(A); return a[:, 0], b[0]
modes = {"X": ("u", "q"), "Y": ("v", "r"), "Z": ("s", "p")}
vs = {k: [] for k in "uvrspq"}
for k in idx:
    u, v = lv(U[k]); r, s_ = lv(V[k]); p, q = lv(W[k])
    for n, x in zip("uvrspq", (u, v, r, s_, p, q)): vs[n].append(of.get(line(x), "other"))
print("frames holding the [1,1,1] vectors, with multiplicity (mode: role: frame counts):")
for m, (a, b) in modes.items():
    print(f"  mode {m}: {a}: {dict(Counter(vs[a]))};  {b}: {dict(Counter(vs[b]))}")
print("|inner product| between frames: " + ", ".join(f"{a},{b}: {sorted(set(np.round(np.abs(Fr_[a] @ Fr_[b].T).ravel(), 3).tolist()))}" for a, b in itertools.combinations(Fr_, 2)))
mono = lambda g, tol=1e-9: np.all(np.sum(np.abs(g) > tol, 0) == 1) and np.all(np.sum(np.abs(g) > tol, 1) == 1)
norm = lambda g: g / abs(np.linalg.det(g)) ** .25
print("elements acting by signed permutations in each frame (id slot of 32, by mode):")
for m in "XYZ":
    print(f"  mode {m}: " + ", ".join(f"{n}: {sum(bool(mono(F @ norm(M(e[m])) @ F.T)) for e in el if e['slot'] == 'id')}" for n, F in Fr_.items()))
print("frame triples (A, B, C) by the number of the 64 elements acting by signed permutations in all three modes:")
tab = Counter(); best = []
for a, b, c in itertools.product(Fr_, repeat=3):
    A, B, C = Fr_[a], Fr_[b], Fr_[c]; n = 0
    for e in el:
        X, Y, Z = map(norm, (M(e['X']), M(e['Y']), M(e['Z'])))
        if e['slot'] == 'id': imgs = (A @ X @ A.T, B @ Y @ B.T, C @ Z @ C.T)
        else: imgs = (A @ X @ C.T, B @ Y @ B.T, C @ Z @ A.T)
        n += all(mono(g) for g in imgs)
    tab[n] += 1; best.append((n, a, b, c))
print("  ", sorted(tab.items(), reverse=True))
for r in sorted(best, reverse=True)[:12]: print("   ", r)
json.dump(sorted(best, reverse=True), open(sys.argv[3], 'w')) if len(sys.argv) > 3 else None
