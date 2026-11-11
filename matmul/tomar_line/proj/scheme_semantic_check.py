#!/usr/bin/env python3
"""Independent check of a bilinear scheme by running it: C = A B on random integer matrices, exact rationals.

Shares no code with kron_reduce.py and uses no numpy.  Product t is (sum u_t[i n1 + j] A[i][j]) times
(sum v_t[j n2 + k] B[j][k]); entry C[i][k] is sum_t w_t[k n0 + i] m_t (the catalog's convention).
A wrong scheme passes one trial with probability at most 2 / R for entries drawn from R values
(Schwartz-Zippel), so this is a strong randomized test, not a proof; the proof is the Brent check.
The script also changes one coefficient and requires the changed scheme to FAIL (negative control).
usage: scheme_semantic_check.py SCHEME.json [TRIALS] [SEED]
"""
import sys, json, random, time
from fractions import Fraction

def run(n, U, V, W, rng, R):
    n0, n1, n2 = n
    A = [[rng.randrange(-R, R + 1) for _ in range(n1)] for _ in range(n0)]
    B = [[rng.randrange(-R, R + 1) for _ in range(n2)] for _ in range(n1)]
    a = [x for row in A for x in row]; b = [x for row in B for x in row]
    prods = []
    for ut, vt in zip(U, V):
        prods.append(sum(c * a[i] for i, c in ut) * sum(c * b[i] for i, c in vt))
    C = [[Fraction(0)] * n2 for _ in range(n0)]
    for wt, mt in zip(W, prods):
        if mt:
            for idx, c in wt:
                k, i = divmod(idx, n0)
                C[i][k] += c * mt
    bad = 0
    for i in range(n0):
        for k in range(n2):
            if C[i][k] != sum(A[i][j] * B[j][k] for j in range(n1)): bad += 1
    return bad

if __name__ == '__main__':
    path = sys.argv[1]; trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3; seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    t0 = time.time()
    d = json.load(open(path)); n = tuple(d['n'])
    sp = lambda rows: [[(i, Fraction(x)) for i, x in enumerate(row) if x not in (0, '0')] for row in rows]
    U, V, W = sp(d['u']), sp(d['v']), sp(d['w'])
    assert len(U) == len(V) == len(W) == d['m']
    rng = random.Random(seed); R = 10 ** 9
    res = [run(n, U, V, W, rng, R) for _ in range(trials)]
    W2 = [list(row) for row in W]; t = len(W2) // 3; i0, c0 = W2[t][0]; W2[t][0] = (i0, c0 + 1)
    ctrl = run(n, U, V, W2, rng, R)
    name = path.split('/')[-1]
    print(f'{name}: shape {n}, {d["m"]} products; {trials} random products with entries up to 1e9: wrong entries per trial {res} -> {"ALL EXACT" if not any(res) else "FAILS"}; one coefficient changed: {ctrl} wrong entries -> {"REJECTED" if ctrl else "ACCEPTED (test is broken)"} ({time.time() - t0:.1f} s)')
