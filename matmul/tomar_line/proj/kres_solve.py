#!/usr/bin/env python3
"""SAT stage of the k-subset re-solve (candidates from src/bin/kres.rs).

For a candidate subset D of k products of an F2 scheme, the residual R = sum of the dropped products lives in the
tensor product of the three factor spans (dimensions da, db, dc < k for a reduction candidate), and tensor rank is
invariant under restriction to the support, so the exact questions are asked on the small da x db x dc tensor:
  reduce : can R be written with k-1 products?  SAT => a scheme of rank r-1 (the full scheme is rebuilt and
           Brent-checked against the matmul tensor and written as .bits);
  alt    : the k-product decompositions of R other than the original (products lexicographically ordered, the
           original blocked, then every found one blocked in turn, up to --alts per candidate) => schemes of rank r
           that no flip reaches (the original is flip-isolated), rebuilt, Brent-checked, deduplicated, written.
CNF: one Tseitin AND per monomial x_s[u] y_s[v] z_s[w], an XOR ladder per cell; solved in-process by python-sat's
CaDiCaL with a conflict budget (--conflicts), or by a cadical process per instance with a time cap (--subprocess, --cap).
usage: kres_solve.py N1 N2 N3 scheme.bits candidates.txt --mode reduce|alt --out DIR [--cap 20] [--alts 20]
       [--max N] [--tag T] [--kmax K] [--quiet]
"""
import sys, os, re, subprocess, itertools, time, argparse
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from project_f2 import load_bits, check, to_bits

CADICAL = '/opt/homebrew/bin/cadical'
try:
    from pysat.solvers import Cadical153 as PySolver   # in-process solving (python-sat); --subprocess forces cadical
except Exception:
    PySolver = None


def vec_of(bits):
    return int(''.join(str(int(b)) for b in bits), 2)


def basis_and_coords(rows):
    """Greedy basis among the rows (as ints); coordinates of every row in that basis by table lookup."""
    basis = []; ech = []  # chosen pivot rows and an echelon copy for the independence test
    for r in rows:
        x = r
        for e in ech:
            if x ^ e < x:
                x ^= e
        if x:
            basis.append(r); ech.append(x); ech.sort(reverse=True)
    d = len(basis)
    table = {}
    for c in range(1 << d):
        v = 0
        for j in range(d):
            if (c >> j) & 1:
                v ^= basis[j]
        table[v] = c
    coords = [table[r] for r in rows]
    return basis, coords


class CNF:
    def __init__(self):
        self.n = 0; self.cl = []
    def var(self):
        self.n += 1; return self.n
    def add(self, *lits):
        self.cl.append(list(lits))
    def and3(self, a, b, c):
        t = self.var(); self.add(-t, a); self.add(-t, b); self.add(-t, c); self.add(t, -a, -b, -c); return t
    def xor2(self, a, b):
        t = self.var(); self.add(-t, a, b); self.add(-t, -a, -b); self.add(t, -a, b); self.add(t, a, -b); return t
    def lex_le(self, xs, ys):
        """xs <=lex ys as bit vectors (same length), implication encoding."""
        e = self.var(); self.add(e)
        for a, b in zip(xs, ys):
            self.add(-e, -a, b)
            e2 = self.var()
            self.add(-e, -a, -b, e2); self.add(-e, a, b, e2)
            e = e2
    def write(self, path):
        with open(path, 'w') as f:
            f.write(f'p cnf {self.n} {len(self.cl)}\n')
            for c in self.cl:
                f.write(' '.join(map(str, c)) + ' 0\n')


def build(R, m, dims, lex=True):
    da, db, dc = dims
    cnf = CNF()
    X = [[cnf.var() for _ in range(da)] for _ in range(m)]
    Y = [[cnf.var() for _ in range(db)] for _ in range(m)]
    Z = [[cnf.var() for _ in range(dc)] for _ in range(m)]
    for u in range(da):
        for v in range(db):
            for w in range(dc):
                acc = None
                for s in range(m):
                    t = cnf.and3(X[s][u], Y[s][v], Z[s][w])
                    acc = t if acc is None else cnf.xor2(acc, t)
                cnf.add(acc if R[u, v, w] else -acc)
    if lex:
        for s in range(m - 1):
            cnf.lex_le(X[s] + Y[s] + Z[s], X[s + 1] + Y[s + 1] + Z[s + 1])
    return cnf, X, Y, Z


class Incremental:
    """One in-process solver per candidate: solve, then add blocking clauses and solve again (alt mode)."""
    def __init__(self, cnf, conflicts):
        self.s = PySolver(bootstrap_with=cnf.cl); self.conf = conflicts
    def solve(self):
        self.s.conf_budget(self.conf)
        r = self.s.solve_limited()
        if r is None:
            return 'timeout', None
        if r is False:
            return 'UNSAT', None
        return 'SAT', set(v for v in self.s.get_model() if v > 0)
    def block(self, lits):
        self.s.add_clause(lits)
    def close(self):
        self.s.delete()


def solve(cnf, path, cap):
    cnf.write(path)
    try:
        p = subprocess.run([CADICAL, '-q', path], capture_output=True, text=True, timeout=cap)
    except subprocess.TimeoutExpired:
        return 'timeout', None
    if p.returncode == 20:
        return 'UNSAT', None
    if p.returncode != 10:
        return f'rc{p.returncode}', None
    model = set()
    for line in p.stdout.splitlines():
        if line.startswith('v'):
            for tok in line.split()[1:]:
                v = int(tok)
                if v > 0:
                    model.add(v)
    return 'SAT', model


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n1', type=int); ap.add_argument('n2', type=int); ap.add_argument('n3', type=int)
    ap.add_argument('bits'); ap.add_argument('cands')
    ap.add_argument('--mode', choices=['reduce', 'alt'], required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--cap', type=float, default=20.0)
    ap.add_argument('--alts', type=int, default=20)
    ap.add_argument('--max', type=int, default=0)
    ap.add_argument('--kmax', type=int, default=99)
    ap.add_argument('--tag', default='k')
    ap.add_argument('--quiet', action='store_true')
    ap.add_argument('--subprocess', action='store_true', help='run cadical as a process per instance instead of in-process pysat')
    ap.add_argument('--conflicts', type=int, default=200000, help='in-process conflict budget per solve (the timeout analogue)')
    a = ap.parse_args()
    inproc = PySolver is not None and not a.subprocess
    n1, n2, n3 = a.n1, a.n2, a.n3
    al, be, ga = load_bits(a.bits, n1, n2, n3)
    r = al.shape[0]
    assert check(al, be, ga, n1, n2, n3), 'input fails the tensor check'
    A = [vec_of(al[t].reshape(-1)) for t in range(r)]
    B = [vec_of(be[t].reshape(-1)) for t in range(r)]
    C = [vec_of(ga[t].reshape(-1)) for t in range(r)]
    wa, wb, wc = n1 * n2, n2 * n3, n1 * n3
    os.makedirs(a.out, exist_ok=True)
    tmp = os.path.join(a.out, f'tmp_{a.tag}_{os.getpid()}.cnf')
    want = 'R' if a.mode == 'reduce' else 'A'
    lines = [l for l in open(a.cands) if l[0] in ('R', 'A')]
    if a.mode == 'alt':
        lines = [l for l in lines]          # R candidates are A candidates too
    else:
        lines = [l for l in lines if l[0] == 'R']
    stats = {'UNSAT': 0, 'SAT': 0, 'timeout': 0, 'other': 0}
    found = {}  # sorted product tuple -> file
    t0 = time.time(); done = 0
    for line in lines:
        m = re.match(r'([RA]) k=(\d+) dims=(\d+),(\d+),(\d+) idx=([\d,]+)', line)
        k = int(m.group(2))
        if k > a.kmax:
            continue
        idx = [int(x) for x in m.group(6).split(',')]
        rows_a = [A[i] for i in idx]; rows_b = [B[i] for i in idx]; rows_c = [C[i] for i in idx]
        ba, ca = basis_and_coords(rows_a); bb, cb = basis_and_coords(rows_b); bc, cc = basis_and_coords(rows_c)
        da, db, dc = len(ba), len(bb), len(bc)
        R = np.zeros((da, db, dc), dtype=np.uint8)
        for t in range(k):
            xu = np.array([(ca[t] >> j) & 1 for j in range(da)], dtype=np.uint8)
            yv = np.array([(cb[t] >> j) & 1 for j in range(db)], dtype=np.uint8)
            zw = np.array([(cc[t] >> j) & 1 for j in range(dc)], dtype=np.uint8)
            R ^= np.einsum('u,v,w->uvw', xu, yv, zw)
        mm = k - 1 if a.mode == 'reduce' else k
        cnf, X, Y, Z = build(R, mm, (da, db, dc))
        blocked = 0
        def lexkey(t):  # the CNF's lex order: X bits j = 0.., then Y, then Z
            xu, yv, zw = t
            return tuple((xu >> j) & 1 for j in range(da)) + tuple((yv >> j) & 1 for j in range(db)) + tuple((zw >> j) & 1 for j in range(dc))
        orig_key = tuple(sorted((A[i], B[i], C[i]) for i in range(r)))
        if a.mode == 'alt':
            # block the original decomposition, in the order the lex constraint imposes
            orig = sorted(zip(ca, cb, cc), key=lexkey)
            lits = []
            for s, (xu, yv, zw) in enumerate(orig):
                for j in range(da): lits.append(-X[s][j] if (xu >> j) & 1 else X[s][j])
                for j in range(db): lits.append(-Y[s][j] if (yv >> j) & 1 else Y[s][j])
                for j in range(dc): lits.append(-Z[s][j] if (zw >> j) & 1 else Z[s][j])
            cnf.add(*lits)
        rounds = a.alts if a.mode == 'alt' else 1
        inc = Incremental(cnf, a.conflicts) if inproc else None
        for rd in range(rounds):
            status, model = inc.solve() if inproc else solve(cnf, tmp, a.cap)
            if status != 'SAT':
                stats[status if status in stats else 'other'] += 1
                break
            stats['SAT'] += 1
            # rebuild the new products in the ambient space
            new = []
            for s in range(mm):
                xu = sum(1 << j for j in range(da) if X[s][j] in model)
                yv = sum(1 << j for j in range(db) if Y[s][j] in model)
                zw = sum(1 << j for j in range(dc) if Z[s][j] in model)
                xa = 0; yb = 0; zc = 0
                for j in range(da):
                    if (xu >> j) & 1: xa ^= ba[j]
                for j in range(db):
                    if (yv >> j) & 1: yb ^= bb[j]
                for j in range(dc):
                    if (zw >> j) & 1: zc ^= bc[j]
                new.append((xa, yb, zc))
            keep = [t for t in range(r) if t not in set(idx)]
            prods = [(A[t], B[t], C[t]) for t in keep] + [p for p in new if p[0] and p[1] and p[2]]
            # cancel duplicated products (equal rank-1 terms sum to zero over F2)
            cnt = {}
            for p in prods: cnt[p] = cnt.get(p, 0) + 1
            prods = [p for p, c in cnt.items() if c % 2 == 1]
            rk = len(prods)
            def tobits(v, w):
                return np.array([(v >> (w - 1 - j)) & 1 for j in range(w)], dtype=np.uint8)
            al2 = np.array([tobits(p[0], wa) for p in prods]).reshape(rk, n1, n2)
            be2 = np.array([tobits(p[1], wb) for p in prods]).reshape(rk, n2, n3)
            ga2 = np.array([tobits(p[2], wc) for p in prods]).reshape(rk, n1, n3)
            ok = check(al2, be2, ga2, n1, n2, n3)
            key = tuple(sorted(prods))
            if ok and key == orig_key:
                stats['same'] = stats.get('same', 0) + 1
            elif ok and key not in found:
                name = f'{a.tag}_{a.mode}_r{rk}_{len(found):05d}.bits'
                open(os.path.join(a.out, name), 'w').write(to_bits(al2, be2, ga2) + '\n')
                found[key] = name
                if rk < r:
                    print('!' * 60); print(f'RANK {rk} < {r}: {name} from candidate {line.strip()}'); print('!' * 60)
                elif not a.quiet:
                    print(f'  alt rank {rk}: {name} from {line.strip()}')
            elif not ok:
                print(f'  BUG: rebuilt scheme fails the tensor check for {line.strip()}')
            # block this assignment and continue (alt mode)
            if a.mode == 'alt':
                lits = []
                for s in range(mm):
                    for v in X[s] + Y[s] + Z[s]:
                        lits.append(-v if v in model else v)
                if inproc:
                    inc.block(lits)
                else:
                    cnf.add(*lits)
                blocked += 1
            else:
                break
        if inc is not None:
            inc.close()
        done += 1
        if a.max and done >= a.max:
            break
        if not a.quiet and done % 500 == 0:
            print(f'c {done} candidates, {stats}, {len(found)} schemes, {time.time() - t0:.0f} s', flush=True)
    if os.path.exists(tmp): os.remove(tmp)
    print(f'c done: {done} candidates, {stats}, {len(found)} distinct schemes written to {a.out}, {time.time() - t0:.0f} s ({"in-process pysat" if inproc else "cadical processes"})')


if __name__ == '__main__':
    main()
