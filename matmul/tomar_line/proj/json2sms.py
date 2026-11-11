#!/usr/bin/env python3
"""Write a catalog-convention scheme as PLinOpt's PREFIX_{L,R,P}.sms over Q, then check the written files.

Input: JSON (or .json.gz) with n = [n0, n1, n2], m, u, v, w, where product t is
(sum u_t[i n1 + j] A[i][j]) (sum v_t[j n2 + k] B[j][k]) and w indexes C transposed (C[i][k] gets w_t[k n0 + i]).
Output: L is m x (n0 n1) on vec(A) row-major, R is m x (n1 n2) on vec(B) row-major, P is (n0 n2) x m giving
vec(C) row-major, so P[i n2 + k][t] = w_t[k n0 + i]; entries are integers or a/b; header "rows cols R", end "0 0 0",
an optional comment line on top (as in PLinOpt's data/32x32x32_15096_*.sms).
The check reads the three files back with its own parser and runs the scheme on random integer matrices
(entries up to 1e9, exact rationals); a copy with one P entry changed must fail (negative control).
usage: json2sms.py SCHEME.json[.gz] OUT_PREFIX [--comment TEXT] [--trials T] [--seed S]
"""
import sys, json, gzip, random, time
from fractions import Fraction

def load(path):
    f = gzip.open(path, 'rt') if path.endswith('.gz') else open(path)
    d = json.load(f)
    n0, n1, n2 = d['n']; m = d['m']
    fr = lambda rows: [[Fraction(x) for x in row] for row in rows]
    U, V, W = fr(d['u']), fr(d['v']), fr(d['w'])
    assert len(U) == len(V) == len(W) == m
    assert all(len(r) == n0 * n1 for r in U) and all(len(r) == n1 * n2 for r in V) and all(len(r) == n0 * n2 for r in W)
    return (n0, n1, n2), m, U, V, W

def write(path, rows, cols, entries, comment):
    with open(path, 'w') as f:
        if comment:
            f.write('# ' + comment + '\n')
        f.write(f'{rows} {cols} R\n')
        for i, j, c in entries:
            f.write(f'{i + 1} {j + 1} {c}\n')
        f.write('0 0 0\n')

def read(path):
    M = None
    for ln in open(path):
        p = ln.split()
        if not p or p[0].startswith('#'):
            continue
        if M is None:
            rows, cols = int(p[0]), int(p[1]); M = {}; continue
        if p[0] == '0' and p[1] == '0':
            break
        M[(int(p[0]) - 1, int(p[1]) - 1)] = Fraction(p[2])
    return rows, cols, M

def run(n, L, R, P, m, rng, Rng):
    n0, n1, n2 = n
    A = [rng.randrange(-Rng, Rng + 1) for _ in range(n0 * n1)]
    B = [rng.randrange(-Rng, Rng + 1) for _ in range(n1 * n2)]
    la = [Fraction(0)] * m; rb = [Fraction(0)] * m
    for (t, j), c in L.items(): la[t] += c * A[j]
    for (t, j), c in R.items(): rb[t] += c * B[j]
    prod = [x * y for x, y in zip(la, rb)]
    C = [Fraction(0)] * (n0 * n2)
    for (r, t), c in P.items(): C[r] += c * prod[t]
    bad = 0
    for i in range(n0):
        for k in range(n2):
            if C[i * n2 + k] != sum(A[i * n1 + j] * B[j * n2 + k] for j in range(n1)): bad += 1
    return bad

def main(a):
    src, out = a[0], a[1]
    comment = a[a.index('--comment') + 1] if '--comment' in a else ''
    trials = int(a[a.index('--trials') + 1]) if '--trials' in a else 2
    seed = int(a[a.index('--seed') + 1]) if '--seed' in a else 11
    t0 = time.time()
    n, m, U, V, W = load(src); n0, n1, n2 = n
    tag = f'<{n0}x{n1}x{n2}:{m}>'
    for side, word, rows, cols, ent in (
            ('L', 'Left', m, n0 * n1, [(t, j, c) for t, r in enumerate(U) for j, c in enumerate(r) if c]),
            ('R', 'Right', m, n1 * n2, [(t, j, c) for t, r in enumerate(V) for j, c in enumerate(r) if c]),
            ('P', 'Product', n0 * n2, m, sorted((i * n2 + k, t, c) for t, r in enumerate(W)
                                              for idx, c in enumerate(r) if c for k, i in [divmod(idx, n0)]))):
        cm = f'{word} HM matrix of {tag}' + (', ' + comment if comment else '')
        write(f'{out}_{side}.sms', rows, cols, ent, cm)
    (rl, cl, L), (rr, cr, R), (rp, cp, P) = (read(f'{out}_{s}.sms') for s in 'LRP')
    assert (rl, cl, rr, cr, rp, cp) == (m, n0 * n1, m, n1 * n2, n0 * n2, m)
    rng = random.Random(seed)
    res = [run(n, L, R, P, m, rng, 10 ** 9) for _ in range(trials)]
    P2 = dict(P); key = sorted(P2)[len(P2) // 2]; P2[key] += 1
    ctrl = run(n, L, R, P2, m, rng, 10 ** 9)
    nnz = (len(L), len(R), len(P))
    ok = all(b == 0 for b in res) and ctrl > 0
    print(f'{out}_{{L,R,P}}.sms: {tag}, nonzeros L {nnz[0]} R {nnz[1]} P {nnz[2]}; wrong entries per trial {res}'
          f' -> {"ALL EXACT" if all(b == 0 for b in res) else "WRONG"}; changed P entry: {ctrl} wrong'
          f' -> {"REJECTED" if ctrl else "NOT REJECTED"} ({time.time() - t0:.1f} s)')
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main(sys.argv[1:])
