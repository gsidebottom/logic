#!/usr/bin/env python3
"""Kronecker-span rank of bilinear schemes: the 2-reducibility bound, on whole catalogs.
(Prior art: this is the 2-reducibility test of LITA -- K. Khoruzhii, L. Serafin, P. Gelss, S. Pokutta, "Local
Improvements to Trilinear Aggregation", github.com/khoruzhii/lita, src/reduce.h -- a strict generalization of the
Kauers-Moosbauer reduction; nothing here is a new test.)

A scheme T = sum_t u_t (x) v_t (x) w_t needs no more products than the dimension of the span of the
Kronecker products of ANY two of its slots (keep a basis of the span, fold the others into the third
slot).  Kauers-Moosbauer's reduction is the special case where the dependent products share a factor;
a dependency whose products share nothing is invisible to it.  This scans scheme files in Perminov's
JSON format (keys n, m, u, v, w; entries integers or "p/q" strings) and reports, per scheme,
  * over F2 (integer schemes only): the products surviving mod 2 and the rank of the three Kronecker
    spans of the mod-2 image -- the minimum is an upper bound on the rank over F2;
  * over Q: the rank of the three Kronecker spans.  Full rank mod 2 certifies full rank over Q; the
    rest are decided on the Gram matrix (V V^T o W W^T, same rank over Q) modulo the prime 2^31 - 1,
    where full rank is again a certificate and a deficit is a claim to confirm.
A scheme is FLAGGED when either bound is below its number of products.
Formats: Perminov's JSON, Mathematica nested lists (.m), Maple TriadSet (.mpl), products of linear forms (.exp).
Every deficit is classified: 'flip-visible' when some dependent set of products shares a factor in one of the
two slots (the reduction the flip graph tests), 'NOT flip-visible' otherwise.
usage: kron_rank_scan.py [--workers W] [--out CSV] [--maxrank M] [--ext json,m,mpl,exp] FILE_OR_DIR ...
"""
import sys, os, json, math, re
from fractions import Fraction
from multiprocessing import Pool

P = 2147483647

def frac(x):
    return Fraction(x) if not isinstance(x, str) else Fraction(x.replace(' ', ''))

def int_rows(M):
    """Rows scaled to integer vectors (a nonzero scaling of a row changes no rank)."""
    out, integral = [], True
    for row in M:
        fr = [frac(x) for x in row]
        den = 1
        for f in fr: den = den * f.denominator // math.gcd(den, f.denominator)
        if den != 1: integral = False
        out.append([int(f * den) for f in fr])
    return out, integral

def rank2(rows):
    piv = {}
    for v in rows:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; break
    return len(piv)

def kron2(A, B, nb):
    """Rows a_t (x) b_t mod 2 as integers; A, B lists of bitmasks."""
    out = []
    for a, b in zip(A, B):
        k = 0; i = 0
        while a:
            if a & 1: k |= b << (i * nb)
            a >>= 1; i += 1
        out.append(k)
    return out

def rank_mod_p(G):
    import numpy as np
    M = np.array(G, dtype=np.int64) % P
    r = M.shape[0]; rank = 0; row = 0
    for col in range(M.shape[1]):
        if row >= r: break
        nz = np.nonzero(M[row:, col])[0]
        if nz.size == 0: continue
        piv = row + int(nz[0])
        if piv != row: M[[row, piv]] = M[[piv, row]]
        inv = pow(int(M[row, col]), P - 2, P)
        M[row, col:] = (M[row, col:] * inv) % P
        f = M[row + 1:, col].copy()
        idx = np.nonzero(f)[0]
        if idx.size:
            M[row + 1 + idx, col:] = (M[row + 1 + idx, col:] - np.outer(f[idx], M[row, col:])) % P
        row += 1; rank += 1
    return rank

NUM = re.compile(r'-?\d+(?:/\d+)?')

def load_m(text):
    """Mathematica nested lists: {{U, V, W}, ...}, each factor a matrix given by rows."""
    t = text.replace('{', '[').replace('}', ']')
    data = json.loads(NUM.sub(lambda g: '"' + g.group(0) + '"', t))
    F = [[[x for row in p[s] for x in row] for p in data] for s in range(3)]
    n = (len(data[0][0]), len(data[0][0][0]), len(data[0][1][0]))
    return n, F

MPL = re.compile(r'Matrix\(\s*(\d+)\s*,\s*(\d+)\s*,\s*\[\s*\[(.*?)\]\s*\]\s*\)', re.S)

TOK = re.compile(r'\s*(\d+|\*\*|[-+*/()])')
SIMPLE = re.compile(r'^-?\d+(/\d+)?$')

def arith(s):
    """Exact value of an arithmetic expression (+ - * / ** and parentheses over the integers); some of the
    catalog's Maple files write entries as 1-0, -0+1, (1), 1*2, +-1/8*0+1/8.  No eval: the files are data."""
    if SIMPLE.match(s): return s
    toks = TOK.findall(s)
    assert ''.join(toks) == re.sub(r'\s', '', s), 'unparsed entry: ' + s[:40]
    pos = [0]
    def peek(): return toks[pos[0]] if pos[0] < len(toks) else None
    def take():
        pos[0] += 1; return toks[pos[0] - 1]
    def atom():
        t = take()
        if t == '(':
            v = expr(); assert take() == ')', 'parenthesis'; return v
        if t == '-': return -power()          # a sign binds less tightly than a power: -2**2 = -4
        if t == '+': return power()
        return Fraction(int(t))
    def power():
        v = atom()
        if peek() == '**':
            take(); e = take(); assert e.isdigit(), 'exponent'
            v = v ** int(e)
        return v
    def term():
        v = power()
        while peek() in ('*', '/'):
            if take() == '*': v *= power()
            else: v /= power()
        return v
    def expr():
        v = term()
        while peek() in ('+', '-'):
            if take() == '+': v += term()
            else: v -= term()
        return v
    v = expr()
    assert pos[0] == len(toks), 'trailing tokens: ' + s[:40]
    return str(v)

def load_mpl(text):
    """Maple TriadSet([Triad([Matrix(r, c, [[..],..]), Matrix, Matrix]), ...]) of Sedoglavic's catalog."""
    body = text[text.index('TriadSet'):]
    mats = []
    for r, c, rows in MPL.findall(body):
        flat = [arith(x.strip()) for row in re.split(r'\]\s*,\s*\[', rows) for x in row.split(',')]
        assert len(flat) == int(r) * int(c), 'matrix size'
        mats.append(((int(r), int(c)), flat))
    assert mats and len(mats) % 3 == 0, 'triads'
    assert body.count('Matrix(') == len(mats), 'unparsed matrices'
    F = [[mats[i + s][1] for i in range(0, len(mats), 3)] for s in range(3)]
    n = (mats[0][0][0], mats[0][0][1], mats[1][0][1])
    return n, F

TERM = re.compile(r'([+-]?)(?:(\d+(?:/\d+)?)\*?)?([abc])(\d)(\d)')

def load_exp(text):
    """One product per line as three linear forms in a_ij, b_ij, c_ij (single-digit indices)."""
    prods = []; mx = {'a': [0, 0], 'b': [0, 0], 'c': [0, 0]}
    for line in text.splitlines():
        line = line.replace(' ', '')
        if not line: continue
        rest = TERM.sub('', line)
        assert not rest.strip('()*+-'), 'unparsed: ' + rest[:40]
        p = {'a': {}, 'b': {}, 'c': {}}
        for sg, co, l, i, j in TERM.findall(line):
            v = Fraction(co) if co else Fraction(1)
            if sg == '-': v = -v
            i = int(i); j = int(j)
            p[l][(i, j)] = p[l].get((i, j), 0) + v
            mx[l][0] = max(mx[l][0], i); mx[l][1] = max(mx[l][1], j)
        prods.append(p)
    F = []
    for l in 'abc':
        R, C = mx[l]
        F.append([[str(p[l].get((i, j), 0)) for i in range(1, R + 1) for j in range(1, C + 1)] for p in prods])
    return (mx['a'][0], mx['a'][1], mx['b'][1]), F

def load(path):
    text = open(path).read()
    if path.endswith('.json'):
        d = json.loads(text)
        assert len(d['u']) == d['m']
        return tuple(d['n']), [d['u'], d['v'], d['w']]
    if path.endswith('.m'): return load_m(text)
    if path.endswith('.mpl'): return load_mpl(text)
    if path.endswith('.exp'): return load_exp(text)
    raise ValueError('unknown format')

def rank_rows_p(rows):
    """Rank mod P of a few integer rows (plain Python)."""
    rows = [[x % P for x in r] for r in rows]; rank = 0
    ncol = len(rows[0]) if rows else 0
    for col in range(ncol):
        piv = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], P - 2, P)
        rows[rank] = [(x * inv) % P for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col]:
                f = rows[i][col]
                rows[i] = [(x - f * y) % P for x, y in zip(rows[i], rows[rank])]
        rank += 1
        if rank == len(rows): break
    return rank

def proj_key(row):
    for x in row:
        x %= P
        if x:
            inv = pow(x, P - 2, P)
            return tuple((y * inv) % P for y in row)
    return None

def km_visible(F, bits, idx, r, c, two):
    """Is some dependency of the (r, c) Kronecker products of the kind the flip graph tests: products
    sharing their factor (up to a scalar) in one of the two slots, with dependent factors in the other?
    Returns (shared slot, group size) or None.  two: work mod 2 on the bitmasks, else mod P."""
    for s, o in ((r, c), (c, r)):
        groups = {}
        for t in idx:
            groups.setdefault(bits[s][t] if two else proj_key(F[s][t]), []).append(t)
        for g in groups.values():
            if len(g) < 2: continue
            rk = rank2([bits[o][t] for t in g]) if two else rank_rows_p([F[o][t] for t in g])
            if rk < len(g): return (s, len(g))
    return None

def scan(path):
    os.nice(15)
    try:
        (n1, n2, n3), (du, dv, dw) = load(path)
        m = len(du)
        U, iu = int_rows(du); V, iv = int_rows(dv); W, iw = int_rows(dw)
        assert len(U) == len(V) == len(W) == m
        F = [U, V, W]; lens = [len(U[0]), len(V[0]), len(W[0])]
        integral = iu and iv and iw
        bits = [[sum((x & 1) << i for i, x in enumerate(row)) for row in M] for M in F]
        res = {'path': path, 'n': (n1, n2, n3), 'm': m, 'integral': integral}
        # F2 image (integer schemes): drop the products with a vanishing factor
        keep = [t for t in range(m) if bits[0][t] and bits[1][t] and bits[2][t]]
        RC = [(1, 2), (0, 2), (0, 1)]
        rk2 = []
        for (r, c) in RC:
            rk2.append(rank2(kron2([bits[r][t] for t in keep], [bits[c][t] for t in keep], lens[c])))
        res['r2'] = len(keep); res['rk2'] = rk2
        # Q: full rank mod 2 on all m products is a certificate; otherwise the Gram matrix mod P
        rkq = []
        for di, (r, c) in enumerate(RC):
            if len(keep) == m and rk2[di] == m:
                rkq.append(m); continue
            import numpy as np
            big = max(abs(x) for M in (F[r], F[c]) for row in M for x in row)
            if big * big * max(lens) < 2 ** 62:
                A = np.array(F[r], dtype=np.int64); B = np.array(F[c], dtype=np.int64)
                G = ((A.dot(A.T) % P) * (B.dot(B.T) % P)) % P
            else:
                A = np.array(F[r], dtype=object); B = np.array(F[c], dtype=object)
                GA = A.dot(A.T); GB = B.dot(B.T)
                G = [[int(GA[i][j]) * int(GB[i][j]) % P for j in range(m)] for i in range(m)]
            rkq.append(rank_mod_p(G))
        res['rkq'] = rkq
        vis = []
        for di, (r, c) in enumerate(RC):
            if integral and rk2[di] < len(keep):
                v = km_visible(F, bits, keep, r, c, True)
                vis.append(f'F2 d={di} ' + (f'flip-visible (slot {v[0]} shared by {v[1]})' if v else 'NOT flip-visible'))
            if rkq[di] < m:
                v = km_visible(F, bits, range(m), r, c, False)
                vis.append(f'Q d={di} ' + (f'flip-visible (slot {v[0]} shared by {v[1]})' if v else 'NOT flip-visible'))
        res['vis'] = vis
        return res
    except Exception as e:
        return {'path': path, 'error': repr(e)}

if __name__ == '__main__':
    args = sys.argv[1:]
    workers = 2; out = None; maxrank = None; paths = []; exts = ('.json',)
    i = 0
    while i < len(args):
        if args[i] == '--workers': workers = int(args[i + 1]); i += 2
        elif args[i] == '--out': out = args[i + 1]; i += 2
        elif args[i] == '--maxrank': maxrank = int(args[i + 1]); i += 2
        elif args[i] == '--ext': exts = tuple('.' + e for e in args[i + 1].split(',')); i += 2
        else: paths.append(args[i]); i += 1
    files = []
    for p in paths:
        if os.path.isdir(p):
            for root, _, fs in os.walk(p):
                files += [os.path.join(root, f) for f in fs if f.endswith(exts)]
        else: files.append(p)
    def size(f):
        try: return os.path.getsize(f)
        except OSError: return 0
    if maxrank:
        def mrank(f):
            g = re.search(r'_m(\d+)_', os.path.basename(f))
            return int(g.group(1)) if g else 0
        files = [f for f in files if mrank(f) <= maxrank]
    files.sort(key=size)
    of = open(out, 'w') if out else None
    if of: of.write('path,n1,n2,n3,m,integral,r2,rk2_0,rk2_1,rk2_2,rkq_0,rkq_1,rkq_2,f2_bound,q_bound\n')
    nflag2 = nflagq = done = 0
    with Pool(workers) as pool:
        for res in pool.imap_unordered(scan, files):
            done += 1
            if 'error' in res:
                print('ERROR', res['path'], res['error'], flush=True); continue
            m = res['m']
            if maxrank and m > maxrank: continue
            f2b = min([res['r2']] + res['rk2']) if res['integral'] else None
            qb = min(res['rkq'])
            if of:
                of.write(','.join(map(str, [res['path'], *res['n'], m, int(res['integral']), res['r2'], *res['rk2'], *res['rkq'], '' if f2b is None else f2b, qb])) + '\n'); of.flush()
            if qb < m:
                nflagq += 1
                print(f'FLAG Q  {res["path"]}: {res["n"]} m={m}: Kronecker ranks over Q (mod {P}) {res["rkq"]} -> at most {qb} products; ' + '; '.join(v for v in res['vis'] if v.startswith('Q')), flush=True)
            if f2b is not None and f2b < m:
                nflag2 += 1
                print(f'FLAG F2 {res["path"]}: {res["n"]} m={m}: {res["r2"]} products survive mod 2, Kronecker ranks {res["rk2"]} -> at most {f2b} products over F2; ' + '; '.join(v for v in res['vis'] if v.startswith('F2')), flush=True)
            if done % 200 == 0: print(f'  .. {done}/{len(files)} files', flush=True)
    print(f'scanned {done} files; flagged over Q: {nflagq}; flagged over F2: {nflag2}')
