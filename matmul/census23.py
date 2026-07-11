#!/usr/bin/env python3
"""Flip-mobility census of rank-23 3x3 schemes (flip23 seed selection).

Replicates flip23's engine semantics exactly:
  - canonical gauge: a, b primitive integer vectors with leading
    coefficient > 0; contents and signs folded into c;
  - eligible pair = post-gauge EQUALITY of a slot's factors;
  - solved coincidence (per shared pair (i,j) in slot s, orientation
    (i,j) and (j,i), transfer slot t): dyadic lambda != 0 with
    f_i + lam f_j = mu f_m exactly (mu != 0), lam = +-2^k;
  - nearmiss = distinct targets m per shared pair, summed;
  - Brent-verified (729 equations) before counting.

Inputs: DB .tab files, lifted/*.txt (M/C text), mm23 SMS dir.
Output: CSV rows  file,ok,pa,pb,pc,pairs,coinc,nearmiss,maxc
"""
import sys, os, re, csv
from fractions import Fraction

def gauge(a, b, c):
    """a,b -> primitive/leading-positive; content*sign folded into c."""
    def canon(v):
        from math import gcd
        g = 0
        for x in v: g = gcd(g, abs(x))
        if g == 0: return None, 1
        s = 1
        for x in v:
            if x != 0:
                s = -1 if x < 0 else 1
                break
        return tuple(x // (g * s) for x in v), g * s
    ca, fa = canon(a)
    cb, fb = canon(b)
    if ca is None or cb is None: return None
    cc = tuple(x * fa * fb for x in c)
    if all(x == 0 for x in cc): return None
    return ca, cb, cc

def brent_ok(S):
    for x in range(9):
        for y in range(9):
            want_base = (x % 3 == y // 3)
            for z in range(9):
                s = sum(a[x] * b[y] * c[z] for a, b, c in S)
                want = 1 if (want_base and x // 3 == z // 3 and y % 3 == z % 3) else 0
                if s != want: return False
    return True

def is_dyadic(fr):
    n, d = abs(fr.numerator), fr.denominator
    return n != 0 and (n & (n - 1)) == 0 and (d & (d - 1)) == 0

def census(S):
    """S = list of 23 (a,b,c) gauged integer 9-tuples."""
    slots = [[t[k] for t in S] for k in range(3)]
    pairs = [[], [], []]
    for k in range(3):
        v = slots[k]
        for i in range(23):
            for j in range(i + 1, 23):
                if v[i] == v[j]:
                    pairs[k].append((i, j))
    coinc = 0
    nearmiss = 0
    for k in range(3):
        others = [t for t in range(3) if t != k]
        for (i, j) in pairs[k]:
            ms = set()
            for (oi, oj) in ((i, j), (j, i)):
                for t in others:
                    fi, fj = slots[t][oi], slots[t][oj]
                    for m in range(23):
                        if m == oi or m == oj: continue
                        fm = slots[t][m]
                        # solve fi + lam*fj = mu*fm  (2x2 Cramer + full check)
                        piv = None
                        for p in range(9):
                            for q in range(p + 1, 9):
                                det = fj[p] * (-fm[q]) - fj[q] * (-fm[p])
                                if det != 0:
                                    piv = (p, q, det); break
                            if piv: break
                        if not piv: continue
                        p, q, det = piv
                        nl = (-fi[p]) * (-fm[q]) - (-fi[q]) * (-fm[p])
                        nmu = fj[p] * (-fi[q]) - fj[q] * (-fi[p])
                        if nl == 0 or nmu == 0: continue
                        lam = Fraction(nl, det)
                        if not is_dyadic(lam): continue
                        if all(det * fi[x] + nl * fj[x] - nmu * fm[x] == 0
                               for x in range(9)):
                            coinc += 1
                            ms.add(m)
            nearmiss += len(ms)
    maxc = max(max(abs(x) for x in t[k]) for t in S for k in range(3))
    return [len(pairs[0]), len(pairs[1]), len(pairs[2]),
            sum(len(p) for p in pairs), coinc, nearmiss, maxc]

# ---------- loaders ----------
def load_tab(path):
    rows = []
    for ln in open(path):
        ln = ln.strip()
        if not ln or '---' in ln: continue
        parts = [p.split() for p in ln.split('|')]
        if len(parts) != 3: continue
        rows.append([[int(x) for x in p] for p in parts])
    if len(rows) != 69: return None       # 23 products x 3 rows
    S = []
    for i in range(23):
        blk = rows[3 * i: 3 * i + 3]
        a = tuple(blk[r][0][c] for r in range(3) for c in range(3))
        b = tuple(blk[r][1][c] for r in range(3) for c in range(3))
        # .tab stores the classical Brent convention: third factor
        # transposed; store output-cell-indexed (verified vs Rust)
        c_ = tuple(blk[c][2][r] for r in range(3) for c in range(3))
        S.append((a, b, c_))
    return S

TERM = re.compile(r'([+-])\s*(\w+)')
def load_lifted(path):
    ab = {}
    cout = {}
    for ln in open(path):
        ln = ln.strip()
        m = re.match(r'M(\d+) = \(([^)]*)\) \* \(([^)]*)\)', ln)
        if m:
            def vec(expr):
                v = [0] * 9
                for sg, name in TERM.findall(expr):
                    r, c = int(name[1]) - 1, int(name[2]) - 1
                    v[3 * r + c] += 1 if sg == '+' else -1
                return tuple(v)
            ab[int(m.group(1)) - 1] = (vec(m.group(2)), vec(m.group(3)))
        m = re.match(r'C(\d)(\d) = (.*)', ln)
        if m:
            r, c = int(m.group(1)) - 1, int(m.group(2)) - 1
            for sg, name in TERM.findall(m.group(3)):
                cout.setdefault(int(name[1:]) - 1, [0] * 9)[3 * r + c] += \
                    1 if sg == '+' else -1
    if len(ab) != 23: return None
    return [(ab[i][0], ab[i][1], tuple(cout.get(i, [0] * 9))) for i in range(23)]

def load_sms_dir(d):
    def parse(p):
        rows = None; out = []
        for ln in open(p):
            f = ln.split()
            if not f or ln.startswith('#'): continue
            if rows is None:
                rows = int(f[0]); out = [[0] * (9 if int(f[1]) == 9 else 23)
                                         for _ in range(rows)]
                continue
            i, j = int(f[0]), int(f[1])
            if i == 0 and j == 0: break
            out[i - 1][j - 1] = int(f[2])
        return out
    L = parse(f'{d}/L.sms'); R = parse(f'{d}/R.sms'); P = parse(f'{d}/P.sms')
    return [(tuple(L[i]), tuple(R[i]),
             tuple(P[z][i] for z in range(9))) for i in range(23)]

def process(path):
    if os.path.isdir(path): S = load_sms_dir(path)
    elif path.endswith('.tab'): S = load_tab(path)
    else: S = load_lifted(path)
    if S is None or len(S) != 23:
        return [path, 'loadfail'] + [''] * 7
    G = [gauge(*t) for t in S]
    if any(g is None for g in G):
        return [path, 'gaugefail'] + [''] * 7
    if not brent_ok(S):
        return [path, 'BRENTFAIL'] + [''] * 7
    return [path, 'ok'] + census(G)

if __name__ == '__main__':
    import multiprocessing as mp
    paths = [ln.strip() for ln in sys.stdin if ln.strip()]
    with mp.Pool(int(os.environ.get('J', '8'))) as pool:
        w = csv.writer(sys.stdout)
        w.writerow(['file', 'status', 'pa', 'pb', 'pc', 'pairs',
                    'coinc', 'nearmiss', 'maxc'])
        for row in pool.imap_unordered(process, paths, chunksize=16):
            w.writerow(row)
