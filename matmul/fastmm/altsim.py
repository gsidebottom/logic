# f32 rounding of ordinary and alternative-basis rank-48 plans, by block-level interpretation of the
# straight-line programs.  Control: accurate_262 against bench_fmm's error / classical at n = 1024.
# Usage: altsim.py SETS.json, with SETS = {name: {L, R, P[, CL, CR, CP]: path to .slp}}; CL, CR, CP are
# the changes of basis, L = ALT_L CoB_L, R = ALT_R CoB_R, P = CoB_P ALT_P.  Run with VECLIB_MAXIMUM_THREADS=1.
import sys, re, os, time, json, itertools
import numpy as np
from fractions import Fraction as Fr
from multiprocessing import get_context

TOK = re.compile(r'\s*(\d+|[a-z]\d+|[()+\-*/])')
def tokens(text):
    pos, out = 0, []
    text = text.strip()
    while pos < len(text):
        m = TOK.match(text, pos)
        assert m, text
        out.append(m.group(1))
        pos = m.end()
    return out
class Parser:
    # expr := term (+|- term)*, term := factor (*|/ factor)*, factor := -factor | (expr) | number | name
    def __init__(self, toks):
        self.t, self.i = toks, 0
    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None
    def take(self):
        self.i += 1
        return self.t[self.i - 1]
    def expr(self):
        x = self.term()
        while self.peek() in ('+', '-'):
            op = self.take()
            x = (op, x, self.term())
        return x
    def term(self):
        x = self.factor()
        while self.peek() in ('*', '/'):
            op = self.take()
            y = self.factor()
            if op == '/':
                assert y[0] == 'c', self.t
                y = ('c', 1 / y[1])
            if x[0] == 'c' and y[0] == 'c':
                x = ('c', x[1] * y[1])
            elif y[0] == 'c':
                x = ('*', y[1], x)
            else:
                assert x[0] == 'c', self.t
                x = ('*', x[1], y)
        return x
    def factor(self):
        k = self.take()
        if k == '-':
            x = self.factor()
            return ('c', -x[1]) if x[0] == 'c' else ('n', x)
        if k == '(':
            x = self.expr()
            assert self.take() == ')', self.t
            return x
        if k.isdigit():
            return ('c', Fr(int(k)))
        return ('v', k)
def parse_slp(path):
    prog, tmp = [], [0]
    def emit(n):
        if n[0] == 'v':
            return n[1]
        tmp[0] += 1
        d = f'_{tmp[0]}'
        if n[0] in '+-':
            a, b = emit(n[1]), emit(n[2])
            prog.append((n[0], d, a, b))
        elif n[0] == 'n':
            prog.append(('n', d, emit(n[1]), None))
        elif n[0] == '*':
            c = float(n[1])
            a = emit(n[2])
            prog.append(('=' if c == 1 else 'n' if c == -1 else '*', d, a, c))
        else:
            raise AssertionError(n)
        return d
    for raw in open(path):
        line = raw.split('#')[0].strip().rstrip(';').strip()
        if ':=' not in line:
            continue
        dest, rhs = [s.strip() for s in line.split(':=')]
        p = Parser(tokens(rhs))
        x = p.expr()
        assert p.i == len(p.t), line
        prog.append(('=', dest, emit(x), None))
    return prog
def counts(prog):
    return sum(o[0] in '+-' for o in prog), sum(o[0] == '*' for o in prog)
def run(prog, inputs):
    env = {f'i{k}': v for k, v in enumerate(inputs)}
    for op, d, a, b in prog:
        if op == '+':
            env[d] = env[a] + env[b]
        elif op == '-':
            env[d] = env[a] - env[b]
        elif op == '=':
            env[d] = env[a]
        elif op == 'n':
            env[d] = -env[a]
        else:
            x = env[a]
            env[d] = x * x.dtype.type(b)
    n = 1 + max(int(k[1:]) for k in env if re.fullmatch(r'o\d+', k))
    return [env[f'o{k}'] for k in range(n)]
def split(X):
    b = X.shape[0] // 4
    return [X[i*b:(i+1)*b, j*b:(j+1)*b] for i in range(4) for j in range(4)]
def join(Bs):
    return np.block([[Bs[4*i + j] for j in range(4)] for i in range(4)])
def mul(S, A, B, lev):
    if lev == 0:
        return A @ B
    Sk, Tk = run(S['L'], split(A)), run(S['R'], split(B))
    return join(run(S['P'], [mul(S, x, y, lev - 1) for x, y in zip(Sk, Tk)]))
def conv(prog, X, lev):
    if lev == 0:
        return X
    return join([conv(prog, x, lev - 1) for x in run(prog, split(X))])
def plan(S, A, B, lev):
    if 'CL' not in S:
        return mul(S, A, B, lev)
    return conv(S['CP'], mul(S, conv(S['CL'], A, lev), conv(S['CR'], B, lev), lev), lev)

def load(spec):
    S = {k: parse_slp(p) for k, p in spec.items()}
    return S
def sms(path):
    t = open(path).read().split()
    M = np.zeros((int(t[0]), int(t[1])))
    for i in range(3, len(t) - 2, 3):
        r, c = int(t[i]), int(t[i+1])
        if r == 0: break
        M[r-1, c-1] = float(Fr(t[i+2]))
    return M

SETS = json.load(open(sys.argv[1]))
SCHEMES = {k: load(v) for k, v in SETS.items()}
NS, LEVELS, SEEDS = [1024, 4096], [1, 2, 3], [1, 2, 3]

def gate():
    rng = np.random.default_rng(5)
    for name, S in SCHEMES.items():
        for lev, n in ((1, 16), (2, 64)):
            A, B = rng.integers(-9, 10, (n, n)).astype(np.float64), rng.integers(-9, 10, (n, n)).astype(np.float64)
            e = np.abs(plan(S, A, B, lev) - A @ B).max()
            assert e < 1e-6, (name, lev, e)
    print('gate: every scheme multiplies exactly at 1 and 2 levels', flush=True)

def job(a):
    n, dist, seed = a
    rng = np.random.default_rng(1000 * n + seed + (0 if dist == 'uniform' else 500))
    if dist == 'uniform':
        A, B = rng.uniform(-1, 1, (n, n)), rng.uniform(-1, 1, (n, n))
    else:
        A, B = rng.standard_normal((n, n)), rng.standard_normal((n, n))
    A32, B32 = A.astype(np.float32), B.astype(np.float32)
    C = A32.astype(np.float64) @ B32.astype(np.float64)
    m = np.abs(C).max()
    res = {('classical', 0): float(np.abs((A32 @ B32).astype(np.float64) - C).max() / m)}
    for name, S in SCHEMES.items():
        for lev in LEVELS:
            res[(name, lev)] = float(np.abs(plan(S, A32, B32, lev).astype(np.float64) - C).max() / m)
    return (n, dist, seed), res

if __name__ == '__main__':
    print('programs: name, kernel adds+scalings (L, R, P), conversions (L, R, P), total')
    for name, S in SCHEMES.items():
        k = [counts(S[x]) for x in 'LRP']
        b = [counts(S[x]) for x in ('CL', 'CR', 'CP') if x in S]
        print(f'  {name:18s} kernel {k} = {sum(a+c for a, c in k)}   conversions {b} = {sum(a+c for a, c in b)}', flush=True)
    for name, v in SETS.items():
        if 'CL' in v:
            cs = [np.linalg.cond(sms(v[x].replace('.slp', '.sms'))) for x in ('CL', 'CR', 'CP')]
            print(f'  {name:18s} cond(CoB_L, CoB_R, CoB_P) = ' + ', '.join(f'{c:.2f}' for c in cs), flush=True)
    gate()
    t0 = time.time()
    jobs = [(n, d, s) for n in NS for d in ('uniform', 'normal') for s in SEEDS]
    agg = {}
    with get_context('fork').Pool(10) as pool:
        for key, res in pool.imap_unordered(job, jobs):
            for k, v in res.items():
                agg.setdefault((key[0], key[1]) + k, {})[key[2]] = v
            print('done', key, f'{time.time()-t0:.0f}s', flush=True)
    print('\nerror as a multiple of the classical f32 GEMM (geometric mean of seeds), uniform / normal')
    for n in NS:
        print(f'n = {n}')
        for name in SCHEMES:
            row = []
            for lev in LEVELS:
                cell = []
                for d in ('uniform', 'normal'):
                    r = [agg[(n, d, name, lev)][s] / agg[(n, d, 'classical', 0)][s] for s in SEEDS]
                    cell.append(np.exp(np.mean(np.log(r))))
                row.append(f'L{lev} {cell[0]:7.2f} /{cell[1]:7.2f}')
            print(f'  {name:18s} ' + '   '.join(row), flush=True)
