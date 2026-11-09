#!/usr/bin/env python3
"""Exact symmetry audit of a d8-quotient Brent CNF (hcnf.py): which free-variable permutations are
semantic symmetries (map the reduced equation set to itself) and which are also syntactic (preserve the
XOR-ladder order, i.e. visible to a clause-graph automorphism tool such as satsuma/dejavu).
Candidates: the normalizer of the prescribed group in the permutation sandwich group S4^3, and swaps of
two orbits of the same class.   usage: hsym_audit.py c0,c1,...,c7   (pool shape counts per conjugacy class)"""
import sys, itertools
sys.path.insert(0, '/Users/greg/projects/logic/matmul/x47')
from hcnf import GROUPS, subgroups, act, gcomp, build, reduced_equations, N
G = GROUPS['d8']; Gs = set(G); subs = subgroups(G)
CLASSES = [0, 1, 3, 4, 6, 7, 8, 9]
counts = [int(t) for t in sys.argv[1].split(',')]
shape = [(CLASSES[i], c) for i, c in enumerate(counts) if c]
def pinv(p):
    q = [0] * N
    for i, x in enumerate(p): q[x] = i
    return tuple(q)
def ginv(g): return tuple(pinv(x) for x in g)
def conj(n, g): return gcomp(gcomp(n, g), ginv(n))
S4 = list(itertools.permutations(range(N)))
norm = [n for n in itertools.product(S4, S4, S4) if all(conj(n, g) in Gs for g in G)]
print(f"shape {counts}: normalizer of d8 in S4^3 has {len(norm)} elements ({len(norm)//len(G)} cosets of d8)")
r, rep, nf = build(G, shape)
nn = N * N
# orbit layout: rep product index, K, free-id matrices
orbits = []; p0 = 0
for kidx, cnt in shape:
    K = subs[kidx]
    for _ in range(cnt):
        U = [[rep[p0 * nn + i * N + j] for j in range(N)] for i in range(N)]
        V = [[rep[r * nn + p0 * nn + i * N + j] for j in range(N)] for i in range(N)]
        W = [[rep[2 * r * nn + p0 * nn + i * N + j] for j in range(N)] for i in range(N)]
        orbits.append((kidx, K, U, V, W)); p0 += len(G) // len(K)
assert p0 == r
_, eqs, _ = reduced_equations(G, shape)
eqset = set((tuple(m), rhs) for m, rhs in eqs)
def test(pi):
    sem = syn = 0
    for mons, rhs in eqs:
        img = [tuple(sorted(pi[v] for v in mon)) for mon in mons]
        if (tuple(sorted(img)), rhs) not in eqset: sem += 1
        elif img != sorted(img): syn += 1
    return sem, syn
def block_map(pi, n1, orb):
    kidx, K, U, V, W = orb; x, y, z = n1
    ok = True
    for i in range(N):
        for j in range(N):
            for M, (a, b) in ((U, (x[i], y[j])), (V, (y[i], z[j])), (W, (x[i], z[j]))):
                f, g = M[i][j], M[a][b]
                if f in pi and pi[f] != g: ok = False
                pi[f] = g
    return ok
results = {}
for n in norm:
    if n in Gs: continue
    pi = {}; ok = True
    for orb in orbits:
        K = set(orb[1])
        cands = [gcomp(h, n) for h in G]
        n1 = next((c for c in cands if set(conj(c, k) for k in K) == K), None)
        if n1 is None or not block_map(pi, n1, orb): ok = False; break
    if not ok or len(set(pi.values())) != nf or len(pi) != nf:
        results.setdefault('ill-defined', []).append(n); continue
    sem, syn = test(pi)
    results.setdefault(('semantic' if sem == 0 else 'not a symmetry', 'syntactic' if sem == 0 and syn == 0 else f'ladder-breaking in {syn} eqs'), []).append(n)
for k, v in results.items(): print(f"  normalizer elements outside d8: {len(v):3d} {k}")
# orbit swaps within a class
swaps = {}
for a, b in itertools.combinations(range(len(orbits)), 2):
    if orbits[a][0] != orbits[b][0]: continue
    pi = {}
    for Ma, Mb in zip(orbits[a][2:], orbits[b][2:]):
        for i in range(N):
            for j in range(N): pi[Ma[i][j]] = Mb[i][j]; pi[Mb[i][j]] = Ma[i][j]
    for orb in orbits:
        if orb is orbits[a] or orb is orbits[b]: continue
        for M in orb[2:]:
            for i in range(N):
                for j in range(N): pi[M[i][j]] = M[i][j]
    sem, syn = test(pi)
    swaps.setdefault((orbits[a][0], 'semantic' if sem == 0 else 'NOT', 'syntactic' if syn == 0 else f'ladder-breaking in {syn} eqs'), 0)
    swaps[(orbits[a][0], 'semantic' if sem == 0 else 'NOT', 'syntactic' if syn == 0 else f'ladder-breaking in {syn} eqs')] += 1
for k, v in swaps.items(): print(f"  orbit swaps in class K{k[0]}: {v} pairs, {k[1]}, {k[2]}")
