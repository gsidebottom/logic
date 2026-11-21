#!/usr/bin/env python3
"""Build the shared-factor ("serendipitous", Perminov arXiv:2606.02480) Kronecker product s1 (x) <a,b,c> as an
explicit scheme and check Brent's equations exactly (integer arithmetic, every equation).
usage: serendip_build.py CATALOG_DIR S1.json a b c OUT.json.gz
s2 and the replacement schemes <a,b,g c>, <g a,b,c>, <a,g b,c> are the lowest-rank integer schemes found in
CATALOG_DIR (trivial scheme when a dimension is 1).  Integer coefficients only.  Reads data only."""
import sys, os, re, json, gzip, itertools
from fractions import Fraction

def rotate(n, u, v, w):                           # as in scheme_orient.py
    return [n[1], n[2], n[0]], v, w, u

def transpose(n, u, v, w):
    n0, n1, n2 = n
    tr = lambda rows, r, c: [[row[b * r + a] for a in range(r) for b in range(c)] for row in rows]
    return [n0, n2, n1], tr(w, n0, n2), tr(v, n2, n1), tr(u, n1, n0)

def load(path):
    d = json.load(open(path))
    cv = lambda M: [[Fraction(str(x)) for x in row] for row in M]
    u, v, w = cv(d['u']), cv(d['v']), cv(d['w'])
    assert all(x.denominator == 1 for M in (u, v, w) for row in M for x in row), 'not integer: ' + path
    return list(d['n']), *[[[int(x) for x in row] for row in M] for M in (u, v, w)]

def trivial(a, b, c):
    u, v, w = [], [], []
    for i, j, k in itertools.product(range(a), range(b), range(c)):
        x = [0] * (a * b); x[i * b + j] = 1; y = [0] * (b * c); y[j * c + k] = 1; z = [0] * (c * a); z[k * a + i] = 1
        u.append(x); v.append(y); w.append(z)
    return [a, b, c], u, v, w

def orient(s, target):
    for plan in ([], ['r'], ['r', 'r'], ['t'], ['t', 'r'], ['t', 'r', 'r']):
        t = s
        for o in plan: t = rotate(*t) if o == 'r' else transpose(*t)
        if list(t[0]) == list(target): return t
    raise SystemExit('no orientation')

def check(s):
    n, u, v, w = s; T = {}
    for x, y, z in zip(u, v, w):
        xs = [(i, a) for i, a in enumerate(x) if a]; ys = [(i, a) for i, a in enumerate(y) if a]
        zs = [(i, a) for i, a in enumerate(z) if a]
        for i, a in xs:
            for j, b in ys:
                ab = a * b
                for k, c in zs:
                    T[i, j, k] = T.get((i, j, k), 0) + ab * c
    E = {(i * n[1] + j, j * n[2] + k, k * n[0] + i) for i in range(n[0]) for j in range(n[1]) for k in range(n[2])}
    return all((val == 1) if key in E else (val == 0) for key, val in T.items()) and all(key in T for key in E)

class Catalog:
    def __init__(self, root):
        self.best = {}
        for r, _, fs in os.walk(root):
            for f in fs:
                m = re.match(r'(\d+)x(\d+)x(\d+)_m(\d+)_.*(?<!_reduced)\.json$', f)
                if m and ('_Z.' in f or '_ZT' in f):
                    key = tuple(sorted(map(int, m.group(1, 2, 3)))); rank = int(m.group(4))
                    if rank < self.best.get(key, (10**9,))[0]: self.best[key] = (rank, os.path.join(r, f))
    def get(self, a, b, c):
        if min(a, b, c) == 1: return trivial(a, b, c)
        rank, path = self.best[tuple(sorted((a, b, c)))]
        s = orient(load(path), (a, b, c)); assert check(s), path
        return s

class Mat:                                        # r x c integer matrix with column / row block slices
    def __init__(self, rows): self.rows = rows; self.r = len(rows); self.c = len(rows[0]) if rows else 0
    def cols(self, lo, hi): return Mat([row[lo:hi] for row in self.rows])
    def rws(self, lo, hi): return Mat(self.rows[lo:hi])
def mat(row, r, c): return Mat([list(row[i * c:(i + 1) * c]) for i in range(r)])
def kron(x, y):
    return [x.rows[i1][j1] * y.rows[i2][j2] for i1 in range(x.r) for i2 in range(y.r) for j1 in range(x.c) for j2 in range(y.c)]
def vsum(vs):
    out = vs[0][:]
    for v in vs[1:]: out = [p + q for p, q in zip(out, v)]
    return out
def scal(k, v): return [k * x for x in v]

def prop(x, y):                                   # y = s x ?
    nz = [i for i, a in enumerate(x) if a]
    if not nz or [i for i, a in enumerate(y) if a] != nz: return None
    s = Fraction(y[nz[0]], x[nz[0]])
    return s if all(Fraction(y[i]) == s * x[i] for i in nz) else None

def groups(rows):
    d = {}
    for i, row in enumerate(rows):
        nz = [(j, x) for j, x in enumerate(row) if x]
        key = tuple((j, Fraction(x, nz[0][1])) for j, x in nz)
        d.setdefault(key, []).append(i)
    return [g for g in d.values() if len(g) > 1]

def build(cat, s1, a, b, c):
    n, u, v, w = s1; m = len(u)
    s2 = cat.get(a, b, c); r2 = len(s2[1])
    dims1 = [(n[0], n[1]), (n[1], n[2]), (n[2], n[0])]; dims2 = [(a, b), (b, c), (c, a)]
    rank3 = {}
    def r3(slot, g):
        f = [(a, b, g * c), (g * a, b, c), (a, g * b, c)][slot]
        if (slot, g) not in rank3:
            key = tuple(sorted(f))
            rank3[slot, g] = len(trivial(*f)[1]) if min(f) == 1 else cat.best.get(key, (None,))[0]
        return rank3[slot, g]
    def sav(slot, g):                             # largest single replacement inside g free products (no partition here)
        best = (0, 0)
        for h in range(2, g + 1):
            r = r3(slot, h)
            if r is not None and h * r2 - r > best[0]: best = (h * r2 - r, h)
        return best
    cand = sorted(((sav(slot, len(x))[0], slot, x) for slot, M in enumerate((u, v, w)) for x in groups(M)), key=lambda t: -t[0])
    used = set(); chosen = []
    for s0, slot, x in cand:
        free = [i for i in x if i not in used]
        while len(free) > 1:
            s, h = sav(slot, len(free))
            if s <= 0: break
            chosen.append((slot, free[:h])); used.update(free[:h]); free = free[h:]
    U, V, W = [], [], []
    M1 = [[mat(row, *dims1[p]) for row in M] for p, M in enumerate((u, v, w))]
    M2 = [[mat(row, *dims2[p]) for row in M] for p, M in enumerate(s2[1:])]
    for t in range(m):
        if t in used: continue
        for q in range(r2):
            U.append(kron(M1[0][t], M2[0][q])); V.append(kron(M1[1][t], M2[1][q])); W.append(kron(M1[2][t], M2[2][q]))
    for slot, G in chosen:
        g = len(G); t0 = G[0]
        sig = [prop((u, v, w)[slot][t0], (u, v, w)[slot][t]) for t in G]
        assert all(x is not None and x.denominator == 1 for x in sig)
        f = [(a, b, g * c), (g * a, b, c), (a, g * b, c)][slot]
        s3 = cat.get(*f)
        for q in range(len(s3[1])):
            u3 = mat(s3[1][q], f[0], f[1]); v3 = mat(s3[2][q], f[1], f[2]); w3 = mat(s3[3][q], f[2], f[0])
            # the shared factor is x0; x_t = sig_t x0, so product t contributes sig_t x0 (x) y_t (x) z_t and the scale
            # sig_t goes onto one of the two free factors (here always the first free one in u, v, w order)
            if slot == 0:
                Uq = kron(M1[0][t0], u3)
                Vq = vsum([scal(int(sig[i]), kron(M1[1][t], v3.cols(i * c, (i + 1) * c))) for i, t in enumerate(G)])
                Wq = vsum([kron(M1[2][t], w3.rws(i * c, (i + 1) * c)) for i, t in enumerate(G)])
            elif slot == 1:
                Uq = vsum([scal(int(sig[i]), kron(M1[0][t], u3.rws(i * a, (i + 1) * a))) for i, t in enumerate(G)])
                Vq = kron(M1[1][t0], v3)
                Wq = vsum([kron(M1[2][t], w3.cols(i * a, (i + 1) * a)) for i, t in enumerate(G)])
            else:
                Uq = vsum([scal(int(sig[i]), kron(M1[0][t], u3.cols(i * b, (i + 1) * b))) for i, t in enumerate(G)])
                Vq = vsum([kron(M1[1][t], v3.rws(i * b, (i + 1) * b)) for i, t in enumerate(G)])
                Wq = kron(M1[2][t0], w3)
            U.append(Uq); V.append(Vq); W.append(Wq)
    N = [n[0] * a, n[1] * b, n[2] * c]
    return (N, U, V, W), chosen, r2

if __name__ == '__main__':
    cat = Catalog(sys.argv[1]); s1 = load(sys.argv[2]); a, b, c = map(int, sys.argv[3:6])
    assert check(s1), 's1 fails'
    s, chosen, r2 = build(cat, s1, a, b, c)
    n, u, v, w = s
    print('s1', s1[0], len(s1[1]), 'products; s2 <%d,%d,%d> rank %d; plain product %d' % (a, b, c, r2, len(s1[1]) * r2))
    print('groups replaced:', [(('u', 'v', 'w')[sl], len(G)) for sl, G in chosen])
    ok = check(s)
    bad = (n, u, [row[:] for row in v], w); k = next(i for i, x in enumerate(bad[2][0]) if x); bad[2][0][k] += 1
    print('format %dx%dx%d rank %d: Brent (all %d equations, exact integers): %s; one changed coefficient: %s'
          % (*n, len(u), (n[0] * n[1]) * (n[1] * n[2]) * (n[2] * n[0]), 'PASS' if ok else 'FAIL', 'REJECTED' if not check(bad) else 'ACCEPTED (checker broken)'))
    if ok:
        with gzip.open(sys.argv[6], 'wt') as fh: json.dump({'n': n, 'm': len(u), 'z2': False, 'u': u, 'v': v, 'w': w}, fh)
