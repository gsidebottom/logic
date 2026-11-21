#!/usr/bin/env python3
"""Independent check of a scheme file (catalog layout, dense or sparse rows, .json or .json.gz) on random
matrices modulo several primes: C = A B must come out of sum_t (u_t . A)(v_t . B) w_t.  Pure Python, no NumPy.
A different method from src/bin/kronexact.rs (which evaluates every Brent equation in integers); a pass here
is probabilistic and only meant as a second opinion from other code.  One changed coefficient must fail.

usage: python3 -I scheme_modp_sparse.py SCHEME.json[.gz] [TRIALS]
"""
import gzip, json, random, sys, time
from fractions import Fraction
PRIMES = [2147483647, 998244353, 18446744069414584321, 1000000007]


def load(path):
    d = json.load(gzip.open(path, 'rt') if path.endswith('.gz') else open(path))
    rows = []
    for key in 'uvw':
        out = []
        for r in d[key]:
            if r and isinstance(r[0], dict):
                out.append([(e['index'], Fraction(e['value'])) for e in r])
            else:
                out.append([(i, Fraction(x)) for i, x in enumerate(r) if x != 0])
        rows.append(out)
    return d['n'], d['m'], rows


def wrong(n, rows, p, rng):
    n0, n1, n2 = n
    red = [[[(i, x.numerator * pow(x.denominator, -1, p) % p) for i, x in r] for r in rows[s]] for s in range(3)]
    a = [rng.randrange(p) for _ in range(n0 * n1)]
    b = [rng.randrange(p) for _ in range(n1 * n2)]
    c = [0] * (n2 * n0)
    for ru, rv, rw in zip(*red):
        f = sum(x * a[i] for i, x in ru) % p * (sum(x * b[i] for i, x in rv) % p) % p
        if f:
            for i, x in rw: c[i] = (c[i] + f * x) % p
    bad = 0
    for i in range(n0):
        for k in range(n2):
            e = sum(a[i * n1 + j] * b[j * n2 + k] for j in range(n1)) % p
            bad += c[k * n0 + i] != e
    return bad


def main():
    path = sys.argv[1]; trials = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    t0 = time.time(); n, m, rows = load(path)
    assert all(len(rows[s]) == m for s in range(3))
    rng = random.Random(20261120)
    res = []
    for p in PRIMES:
        if any(x.denominator % p == 0 for s in range(3) for r in rows[s] for _, x in r):
            res.append('p=%d: undefined' % p); continue
        res.append('p=%d: %s' % (p, 'correct' if all(wrong(n, rows, p, rng) == 0 for _ in range(trials)) else 'WRONG'))
    t = m // 3; i, x = rows[1][t][0]; rows[1][t][0] = (i, x + 1)
    ctrl = wrong(n, rows, PRIMES[0], rng)
    ok = all(r.endswith('correct') for r in res) and ctrl > 0
    print('%s: <%dx%dx%d:%d> %s; one coefficient changed: %d wrong entries -> %s; %s (%.1f s)' % (
        path.split('/')[-1], *n, m, '; '.join(res), ctrl, 'REJECTED' if ctrl else 'ACCEPTED', 'PASS' if ok else 'FAIL', time.time() - t0))
    sys.exit(0 if ok else 1)


main()
