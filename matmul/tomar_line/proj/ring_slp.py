#!/usr/bin/env python3
"""Straight-line programs for a scheme's three maps that stay in the scheme's own coefficient ring.

PLinOpt's optimizer may divide by constants the matrix does not need (a common factor 3 taken out of an integer
row gives "*2/3").  Here a greedy common-pair elimination only ever forms t = p x + q y with (p, q) a primitive
integer pair, and a row uses g t with g = (row coefficients) / (p, q), so every constant of the program is an
integer or an integer over a denominator that occurs in the matrix: integer matrices get integer programs,
matrices over Z[1/2] get programs whose only divisions are by powers of two.

L and R (m x inputs, short rows) are done directly.  P (outputs x m, long rows) is done through its transpose:
the program for P^T is reversed (Tellegen), which keeps the constants and costs additions(P^T) + m - outputs.

usage: ring_slp.py PREFIX      reads PREFIX_{L,R,P}.sms, writes PREFIX_{L,R,P}.slp (PLinOpt syntax: inputs i0..,
outputs o0.., one assignment per line), re-evaluates each program symbolically against its matrix (exact) and
prints additions, scalings and the set of prime divisors of all denominators used.
       ring_slp.py --check PREFIX    reads the three programs back from the .slp files instead of making them and
runs the same checks: each program equals its matrix exactly and divides only by the matrix's denominator primes.
"""
import sys, heapq, re
from fractions import Fraction
from math import gcd
from collections import defaultdict

def read_sms(path):
    rows = cols = None; M = defaultdict(dict)
    for ln in open(path):
        p = ln.split()
        if not p or p[0].startswith('#'): continue
        if rows is None: rows, cols = int(p[0]), int(p[1]); continue
        if p[0] == '0' and p[1] == '0': break
        M[int(p[0]) - 1][int(p[1]) - 1] = Fraction(p[2])
    return rows, cols, [dict(M.get(r, {})) for r in range(rows)]

def cse(rows, nin):
    """rows: list of {var: Fraction}.  Returns temps [(var, x, p, y, q)] (var = p x + q y, integers, gcd 1, p > 0)
    and the rows rewritten over inputs and temps."""
    scale = []; R = []
    for r in rows:
        s = 1
        for c in r.values(): s = s * c.denominator // gcd(s, c.denominator)
        scale.append(s); R.append({v: int(c * s) for v, c in r.items()})
    def key(x, cx, y, cy):
        if x > y: x, cx, y, cy = y, cy, x, cx
        g = gcd(cx, cy)
        if cx < 0: g = -g
        return (x, cx // g, y, cy // g)
    occ = defaultdict(set)
    for i, r in enumerate(R):
        vs = sorted(r)
        for a in range(len(vs)):
            for b in range(a + 1, len(vs)):
                occ[key(vs[a], r[vs[a]], vs[b], r[vs[b]])].add(i)
    heap = [(-len(s), k) for k, s in occ.items() if len(s) > 1]; heapq.heapify(heap)
    temps = []; nxt = nin
    while heap:
        n, k = heapq.heappop(heap)
        s = occ.get(k)
        if not s or len(s) != -n:
            if s and len(s) > 1: heapq.heappush(heap, (-len(s), k))
            continue
        if len(s) < 2: break
        x, p, y, q = k; t = nxt; nxt += 1; temps.append((t, x, p, y, q)); touched = set()
        for i in list(s):
            r = R[i]; g = r[x] // p
            assert r[x] == g * p and r[y] == g * q
            for u in (x, y):
                for w, cw in r.items():
                    if w != u and not (u == y and w == x):
                        kk = key(u, r[u], w, cw); occ[kk].discard(i); touched.add(kk)
            occ[k].discard(i)
            del r[x], r[y]
            for w, cw in r.items():
                kk = key(t, g, w, cw); occ[kk].add(i); touched.add(kk)
            r[t] = g
        for kk in touched:
            if len(occ[kk]) > 1: heapq.heappush(heap, (-len(occ[kk]), kk))
            elif not occ[kk]: del occ[kk]
    return temps, [{v: Fraction(c, scale[i]) for v, c in r.items()} for i, r in enumerate(R)]

def term(c, name, first):
    s = '-' if c < 0 else ('' if first else '+'); a = abs(c)
    if a == 1: return s + name
    if a.denominator == 1: return f'{s}{name}*{a.numerator}'
    if a.numerator == 1: return f'{s}{name}/{a.denominator}'
    return f'{s}{name}*{a.numerator}/{a.denominator}'

def line(lhs, terms):
    terms = sorted(terms, key=lambda t: t[0] < 0)                    # a positive term first when there is one
    return lhs + ':=' + ''.join(term(c, n, i == 0) for i, (c, n) in enumerate(terms)) + ';'

def direct(rows, nin):
    temps, out = cse(rows, nin)
    nm = lambda v: f'i{v}' if v < nin else f't{v}'
    prog = [(f't{t}', [(Fraction(p), nm(x)), (Fraction(q), nm(y))]) for t, x, p, y, q in temps]
    for i, r in enumerate(out):
        prog.append((f'o{i}', [(c, nm(v)) for v, c in sorted(r.items())] or [(Fraction(0), 'i0')]))
    return prog

def transposed(rows, ncols):
    """Program for the matrix with these rows (nout x ncols) from the CSE of its transpose (ncols x nout)."""
    nout = len(rows); T = [dict() for _ in range(ncols)]
    for i, r in enumerate(rows):
        for j, c in r.items(): T[j][i] = c
    temps, out = cse(T, nout)                                        # nodes: inputs 0..nout-1, temps, rows of T
    # edges consumer <- source with a coefficient; the adjoint of a source is the sum over its consumers
    cons = defaultdict(list)
    for t, x, p, y, q in temps:
        cons[x].append((Fraction(p), f'a{t}')); cons[y].append((Fraction(q), f'a{t}'))
    for j, r in enumerate(out):
        for v, c in r.items(): cons[v].append((c, f'i{j}'))
    prog = []
    for t, x, p, y, q in reversed(temps):
        assert cons[t], 'unused temporary'
        prog.append((f'a{t}', cons[t]))
    for i in range(nout):
        prog.append((f'o{i}', cons[i] or [(Fraction(0), 'i0')]))
    return [(l.replace('a', 't') if l[0] == 'a' else l, [(c, n.replace('a', 't') if n[0] == 'a' else n) for c, n in ts]) for l, ts in prog]

def evaluate(prog, nin):
    val = {f'i{j}': {j: Fraction(1)} for j in range(nin)}
    for lhs, terms in prog:
        acc = defaultdict(Fraction)
        for c, n in terms:
            for j, x in val[n].items(): acc[j] += c * x
        val[lhs] = {j: x for j, x in acc.items() if x}
    return val

def factor_lines(prog, allowed):
    """Take a common factor out of a line when that saves scalings: lhs = g * (sum of (c / g) x), with g one of the
    line's own coefficients and every c / g still over the allowed denominator primes."""
    used = [int(l[1:]) for l, _ in prog if l[0] == 't']; nxt = max(used, default=0) + 1
    out = []
    for lhs, ts in prog:
        base = sum(1 for c, _ in ts if abs(c) != 1); best = (base, None)
        if len(ts) > 1 and base > 1:
            for g in {abs(c) for c, _ in ts if abs(c) != 1}:
                q = [c / g for c, _ in ts]
                if any(not primes(x.denominator) <= allowed for x in q): continue
                cost = 1 + sum(1 for x in q if abs(x) != 1)
                if cost < best[0]: best = (cost, g)
        if best[1] is None: out.append((lhs, ts)); continue
        g = best[1]; aux = f't{nxt}'; nxt += 1
        out.append((aux, [(c / g, n) for c, n in ts])); out.append((lhs, [(g, aux)]))
    return out

def primes(n):
    out = set(); p = 2
    while p * p <= n:
        while n % p == 0: out.add(p); n //= p
        p += 1
    if n > 1: out.add(n)
    return out

TERM = re.compile(r'([+-]?)([a-z]\d+)(?:\*(\d+))?(?:/(\d+))?')

def read_slp(path):
    prog = []
    for ln in open(path):
        ln = ln.split('#')[0].strip().rstrip(';')
        if not ln: continue
        lhs, rhs = ln.split(':='); ts = []; pos = 0
        for mt in TERM.finditer(rhs):
            assert mt.start() == pos, f'cannot parse {ln}'; pos = mt.end()
            c = Fraction(int(mt.group(3) or 1), int(mt.group(4) or 1))
            ts.append((-c if mt.group(1) == '-' else c, mt.group(2)))
        assert pos == len(rhs), f'cannot parse {ln}'
        prog.append((lhs, ts))
    return prog

if __name__ == '__main__':
    check = '--check' in sys.argv
    pre = [a for a in sys.argv[1:] if a != '--check'][0]; tot = [0, 0]
    for side in 'LRP':
        rows, cols, M = read_sms(f'{pre}_{side}.sms')
        mp = set()
        for r in M:
            for c in r.values(): mp |= primes(c.denominator)
        if check:
            prog = read_slp(f'{pre}_{side}.slp')
        else:
            prog = factor_lines(transposed(M, cols) if side == 'P' else direct(M, cols), mp)
        val = evaluate(prog, cols)
        bad = sum(1 for i in range(rows) if val[f'o{i}'] != M[i])
        assert bad == 0, f'{side}: {bad} outputs differ from the matrix'
        adds = sum(len(ts) - 1 for _, ts in prog); scal = sum(1 for _, ts in prog for c, _ in ts if abs(c) != 1 and c != 0)
        dp = set()
        for _, ts in prog:
            for c, _ in ts: dp |= primes(c.denominator)
        assert dp <= mp, f'{side}: program divides by primes {sorted(dp - mp)} the matrix does not have'
        if not check:
            with open(f'{pre}_{side}.slp', 'w') as f:
                for lhs, ts in prog: f.write(line(lhs, ts) + '\n')
        tot[0] += adds; tot[1] += scal
        print(f'{pre.split("/")[-1]}_{side}: {rows} x {cols}; {adds} additions, {scal} scalings; denominator primes of the program {sorted(dp)} (matrix {sorted(mp)}); program = matrix, exactly', flush=True)
    print(f'{pre.split("/")[-1]}: total {tot[0]} additions + {tot[1]} scalings = {sum(tot)}')
