#!/usr/bin/env python3
"""Run a catalog-convention scheme with NON-COMMUTING entries: A and B are matrices whose entries are random 2x2
integer matrices, so each product (sum u A)(sum v B) is a 2x2 matrix product taken in that order.  A scheme that
relied on commutativity would fail here.  Control: the same run with every product taken in the wrong order,
(sum v B)(sum u A), must fail.  Exact integers and rationals; no numpy.
usage: scheme_noncomm_check.py SCHEME.json[.gz] [SEED]
"""
import sys, json, gzip, random, time
from fractions import Fraction

def mm(x, y):  # 2x2 matrices as 4-tuples, row-major
    return (x[0]*y[0] + x[1]*y[2], x[0]*y[1] + x[1]*y[3], x[2]*y[0] + x[3]*y[2], x[2]*y[1] + x[3]*y[3])

def run(n, U, V, W, A, B, swap):
    n0, n1, n2 = n
    C = [[Fraction(0)] * 4 for _ in range(n0 * n2)]
    for ut, vt, wt in zip(U, V, W):
        la = [sum(c * A[i][q] for i, c in ut) for q in range(4)]
        rb = [sum(c * B[i][q] for i, c in vt) for q in range(4)]
        p = mm(rb, la) if swap else mm(la, rb)
        for idx, c in wt:
            k, i = divmod(idx, n0)
            r = C[i * n2 + k]
            for q in range(4): r[q] += c * p[q]
    bad = 0
    for i in range(n0):
        for k in range(n2):
            want = [0] * 4
            for j in range(n1):
                pr = mm(A[i * n1 + j], B[j * n2 + k])
                for q in range(4): want[q] += pr[q]
            if C[i * n2 + k] != want: bad += 1
    return bad

path = sys.argv[1]; seed = int(sys.argv[2]) if len(sys.argv) > 2 else 5
t0 = time.time()
d = json.load(gzip.open(path, 'rt') if path.endswith('.gz') else open(path)); n = tuple(d['n'])
sp = lambda rows: [[(i, Fraction(x)) for i, x in enumerate(row) if x not in (0, '0')] for row in rows]
U, V, W = sp(d['u']), sp(d['v']), sp(d['w'])
rng = random.Random(seed); R = 10 ** 6
A = [tuple(rng.randrange(-R, R + 1) for _ in range(4)) for _ in range(n[0] * n[1])]
B = [tuple(rng.randrange(-R, R + 1) for _ in range(4)) for _ in range(n[1] * n[2])]
ok = run(n, U, V, W, A, B, False); ctrl = run(n, U, V, W, A, B, True)
print(f'{path.split("/")[-1]}: <{n[0]}x{n[1]}x{n[2]}:{d["m"]}> with 2x2-matrix entries: {ok} wrong entries of C'
      f' -> {"CORRECT over non-commuting entries" if ok == 0 else "FAILS"}; products in the wrong order: {ctrl} wrong'
      f' -> {"control fails as it must" if ctrl else "CONTROL DID NOT FAIL"} ({time.time() - t0:.1f} s)')
sys.exit(0 if ok == 0 and ctrl > 0 else 1)
