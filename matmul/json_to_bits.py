#!/usr/bin/env python3
"""Convert a scheme in Perminov's FastMatrixMultiplication JSON format (keys n = [n1, n2, n3], m = rank,
u/v/w = per-product integer coefficient vectors over the row-major entries of A (n1 x n2), B (n2 x n3)
and C (n1 x n3)) to the repository's mod-2 .bits layout (the r alpha blocks, then the r betas, then the
r gammas, row-major, one line), verifying the Brent equations over F2 first.  Coefficients are reduced
mod 2; a product whose factor vanishes mod 2 is dropped (the rank over F2 is reported).  Both gamma
orientations are tried and the one satisfying the equations is written.  Pure Python; run with -I.
usage: json_to_bits.py scheme.json out.bits"""
import sys, json
src, dst = sys.argv[1], sys.argv[2]
d = json.load(open(src))
n1, n2, n3 = d["n"]; r0 = d["m"]
U, V, W = d["u"], d["v"], d["w"]
assert len(U) == len(V) == len(W) == r0, "rank disagrees with the vectors"
assert all(len(x) == n1 * n2 for x in U) and all(len(x) == n2 * n3 for x in V) and all(len(x) == n1 * n3 for x in W)
terms = []
for s in range(r0):
    a = [c % 2 for c in U[s]]; b = [c % 2 for c in V[s]]; c = [x % 2 for x in W[s]]
    if any(a) and any(b) and any(c):
        terms.append((a, b, c))
r = len(terms)
print(f"{src}: <{n1},{n2},{n3}> rank {r0} over Z, {r} products survive mod 2")
def brent(ct):
    bad = 0
    al = [[[t[0][i*n2+k] for k in range(n2)] for i in range(n1)] for t in terms]
    be = [[[t[1][k*n3+j] for j in range(n3)] for k in range(n2)] for t in terms]
    if ct:   # gamma stored as c_(j,i): entry (i,j) of C sits at index j*n1 + i
        ga = [[[t[2][j*n1+i] for j in range(n3)] for i in range(n1)] for t in terms]
    else:
        ga = [[[t[2][i*n3+j] for j in range(n3)] for i in range(n1)] for t in terms]
    for i in range(n1):
        for k in range(n2):
            T = [t for t in range(r) if al[t][i][k]]
            for k2 in range(n2):
                for j in range(n3):
                    T2 = [t for t in T if be[t][k2][j]]
                    for i2 in range(n1):
                        for j2 in range(n3):
                            v = sum(ga[t][i2][j2] for t in T2) & 1
                            if v != int(k == k2 and i == i2 and j == j2): bad += 1
    return bad, al, be, ga
chosen = None
for ct in (False, True):
    bad, al, be, ga = brent(ct)
    print(f"  gamma as c_(j,i)={ct}: {bad} of {n1*n2*n2*n3*n1*n3} Brent equations violated")
    if bad == 0 and chosen is None: chosen = (ct, al, be, ga)
assert chosen is not None, "neither orientation satisfies the Brent equations"
ct, al, be, ga = chosen
bits = ''.join(str(x) for t in range(r) for row in al[t] for x in row) + ''.join(str(x) for t in range(r) for row in be[t] for x in row) + ''.join(str(x) for t in range(r) for row in ga[t] for x in row)
open(dst, 'w').write(bits + '\n')
print(f"wrote {dst}: rank {r}, {len(bits)} bits, gamma read as c_(j,i)={ct}")
