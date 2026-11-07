#!/usr/bin/env python3
"""Capacity constraints (Tomar, arXiv:2610.11823, Lemma 2.1) for F2
matrix-multiplication schemes, and their use in SAT completion.

For a decomposition of <n1,n2,n3> with r terms and a slot X in {a, b, c}:

  forms   for every nonzero linear form f on the slot's space, viewed as
          a matrix of the slot's shape, at least m_X rank(f) terms have
          f(x_s) = 1, where m_X is the third dimension (n3 for a, n1 for
          b, n2 for c): the image of the tensor modulo ker f is the
          matrix f^T (x) I, of rank m_X rank(f).  Exact, no outside fact.
  caps    for a subspace S whose quotient tensor is a smaller format Q,
          at most r - R(Q) terms have x_s in S.  Row directions mu of A
          (S = mu (x) F2^n2) quotient to <n1-1,n2,n3>, column directions
          of A to <n1,n2-1,n3>; rows of B to <n1,n2-1,n3>, columns of B to
          <n1,n2,n3-1>; rows of C to <n1-1,n2,n3>, columns of C to
          <n1,n2,n3-1>.  R(Q) is a LOWER bound taken from the table below
          (provenance in lb_table); the constraint is sound for any valid
          lower bound.

usage:
  capacity.py report N1 N2 N3 scheme.bits            constraints and slack of a scheme
  capacity.py lbtable                                 the lower-bound table used
  capacity.py cnf N1 N2 N3 scheme.bits --freeze a --out F.cnf
              [--drop S] [--card entries,rank1,caps]   completion CNF: the frozen
              slot's factors are constants, the Brent equations are
              quadratic in the other two slots; --card adds the
              constraints on the free slots as cardinality constraints
              (sequential counters)
  capacity.py run F.cnf [--timeout 600] [--seeds 1,2,3]  CaDiCaL on a CNF
"""
import argparse, itertools, math, os, subprocess, sys, time
import numpy as np

CADICAL = '/opt/homebrew/bin/cadical'


# ---------------------------------------------------------------- lower bounds

BASE = {
    # exact or proven lower bounds over F2 with provenance
    (2, 2, 2): (7, 'Winograd 1971 / Hopcroft-Kerr 1971'),
    (2, 2, 3): (11, 'Hopcroft-Kerr 1971: <2,2,n> = ceil(7n/2) over F2'),
    (2, 2, 4): (14, 'Hopcroft-Kerr 1971'),
    (2, 2, 5): (18, 'Hopcroft-Kerr 1971'),
    (2, 3, 3): (15, 'Hopcroft-Kerr 1971 (over F2); Alekseyev 1985 all fields'),
    (2, 3, 4): (19, 'Hopcroft-Kerr 1971 (sketched), proof completed by Wang 2026, arXiv:2603.07280'),
    (3, 3, 3): (20, 'Wang 2026, arXiv:2603.07280 (verified in this repository)'),
}


def lb(n1, n2, n3, memo={}):
    """lower bound on R(<n1,n2,n3>) over F2: the base table, <1,m,p> = mp, and
    the reverse projection lemma R(<n,m,p+1>) >= R(<n,m,p>) + m (and its
    row and inner versions), closed under permutations of the format."""
    key = tuple(sorted((n1, n2, n3)))
    if key in memo:
        return memo[key]
    a, b, c = key
    if a == 1:
        val = (b * c, 'outer product <1,m,p> = mp')
    else:
        best = (max(a * b, b * c, a * c), 'flattening')
        if key in BASE:
            best = max(best, BASE[key], key=lambda x: x[0])
        # reverse projections: <n,m,p> >= <n,m,p-1> + m, >= <n-1,m,p> + m, >= <n,m-1,p> + max(n,p)
        n, m, p = a, b, c
        cands = []
        if p - 1 >= 1:
            v, _ = lb(n, m, p - 1); cands.append((v + m, f'<{n},{m},{p-1}> + {m}'))
        if n - 1 >= 1:
            v, _ = lb(n - 1, m, p); cands.append((v + m, f'<{n-1},{m},{p}> + {m}'))
        if m - 1 >= 1:
            v, _ = lb(n, m - 1, p); cands.append((v + max(n, p), f'<{n},{m-1},{p}> + {max(n, p)}'))
        for cnd in cands:
            if cnd[0] > best[0]:
                best = cnd
        val = best
    memo[key] = val
    return val


# ---------------------------------------------------------------- schemes

def load_bits(path, n1, n2, n3):
    txt = open(path).read().split()[-1]
    bits = np.array([int(ch) for ch in txt], dtype=np.uint8)
    w = n1 * n2 + n2 * n3 + n1 * n3
    assert bits.size % w == 0
    r = bits.size // w
    sa, sb = r * n1 * n2, r * n2 * n3
    return (bits[:sa].reshape(r, n1, n2), bits[sa:sa + sb].reshape(r, n2, n3), bits[sa + sb:].reshape(r, n1, n3))


def rank_f2(M):
    M = (np.array(M, dtype=np.uint8) % 2).copy()
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i; break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
        if r == rows:
            break
    return r


SLOTS = {  # slot -> (shape index pair, m_X, quotient formats of (row direction, column direction))
    'a': None, 'b': None, 'c': None,
}


def slot_info(n1, n2, n3):
    return {
        'a': dict(shape=(n1, n2), m=n3, row_q=(n1 - 1, n2, n3), col_q=(n1, n2 - 1, n3)),
        'b': dict(shape=(n2, n3), m=n1, row_q=(n1, n2 - 1, n3), col_q=(n1, n2, n3 - 1)),
        'c': dict(shape=(n1, n3), m=n2, row_q=(n1 - 1, n2, n3), col_q=(n1, n2, n3 - 1)),
    }


def all_forms(h, w):
    """every nonzero h x w matrix over F2 as (flat bits, rank)"""
    D = h * w
    out = []
    for code in range(1, 1 << D):
        f = np.array([(code >> i) & 1 for i in range(D)], dtype=np.uint8)
        out.append((f, rank_f2(f.reshape(h, w))))
    return out


def in_row_dir(x, mu):
    """x (h x w) lies in mu (x) F2^w: rows outside mu zero, rows in mu equal"""
    rows = [x[k] for k in range(x.shape[0]) if mu[k]]
    zero = all(not x[k].any() for k in range(x.shape[0]) if not mu[k])
    return zero and all(np.array_equal(rows[0], rw) for rw in rows[1:])


def in_col_dir(x, nu):
    return in_row_dir(x.T, nu)


def report(n1, n2, n3, path):
    alpha, beta, gamma = load_bits(path, n1, n2, n3)
    r = alpha.shape[0]
    fac = {'a': alpha, 'b': beta, 'c': gamma}
    info = slot_info(n1, n2, n3)
    print(f'c <{n1},{n2},{n3}> rank {r}: {path}')
    for X in 'abc':
        h, w = info[X]['shape']
        m = info[X]['m']
        F = fac[X].reshape(r, h * w)
        forms = all_forms(h, w)
        Fm = np.stack([f for f, _ in forms])                  # (nf, D)
        ranks = np.array([rk for _, rk in forms])
        par = (Fm @ F.T) % 2                                  # (nf, r): f(x_s)
        counts = par.sum(axis=1)
        need = m * ranks
        viol = int((counts < need).sum())
        slack = counts - need
        by_rank = {}
        for rk in sorted(set(ranks.tolist())):
            sel = ranks == rk
            by_rank[rk] = (int(sel.sum()), int(slack[sel].min()), int((slack[sel] == 0).sum()))
        print(f'c slot {X} ({h}x{w}, m={m}): {len(forms)} forms, violations {viol}; '
              + '; '.join(f'rank {rk}: {n} forms, min slack {mn}, tight {tight}' for rk, (n, mn, tight) in by_rank.items()))
        # caps
        for kind, dim, test, q in (('row', h, in_row_dir, info[X]['row_q']), ('col', w, in_col_dir, info[X]['col_q'])):
            if min(q) < 1:
                continue
            L, prov = lb(*q)
            cap = r - L
            worst = None
            for code in range(1, 1 << dim):
                d = np.array([(code >> i) & 1 for i in range(dim)], dtype=np.uint8)
                cnt = sum(1 for s in range(r) if test(fac[X][s], d))
                if worst is None or cnt > worst[0]:
                    worst = (cnt, code)
            print(f'c   {kind} directions of {X}: quotient <{q[0]},{q[1]},{q[2]}> >= {L} ({prov}) -> at most {cap} terms in a direction; '
                  f'largest count {worst[0]} (direction {worst[1]:0{dim}b}){"  VIOLATION" if worst[0] > cap else ""}')


# ---------------------------------------------------------------- CNF

class CNF:
    def __init__(self):
        self.nv = 0
        self.cl = []
        self.and_cache = {}

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, c):
        self.cl.append(list(c))

    def and2(self, x, y):
        key = (min(x, y), max(x, y))
        if key in self.and_cache:
            return self.and_cache[key]
        m = self.var()
        self.add([-m, x]); self.add([-m, y]); self.add([m, -x, -y])
        self.and_cache[key] = m
        return m

    def xor_chain(self, lits):
        """a literal equal to the XOR of lits (empty -> None)"""
        if not lits:
            return None
        acc = lits[0]
        for l in lits[1:]:
            z = self.var()
            self.add([-z, acc, l]); self.add([-z, -acc, -l]); self.add([z, -acc, l]); self.add([z, acc, -l])
            acc = z
        return acc

    def at_most(self, lits, k):
        """sequential counter (Sinz 2005): at most k of lits are true"""
        n = len(lits)
        if k >= n:
            return
        if k == 0:
            for l in lits:
                self.add([-l])
            return
        s = [[self.var() for _ in range(k)] for _ in range(n - 1)]
        self.add([-lits[0], s[0][0]])
        for j in range(1, k):
            self.add([-s[0][j]])
        for i in range(1, n - 1):
            self.add([-lits[i], s[i][0]])
            self.add([-s[i - 1][0], s[i][0]])
            for j in range(1, k):
                self.add([-lits[i], -s[i - 1][j - 1], s[i][j]])
                self.add([-s[i - 1][j], s[i][j]])
            self.add([-lits[i], -s[i - 1][k - 1]])
        self.add([-lits[n - 1], -s[n - 2][k - 1]])

    def at_least(self, lits, k):
        if k <= 0:
            return
        self.at_most([-l for l in lits], len(lits) - k)

    def write(self, path):
        with open(path, 'w') as f:
            f.write(f'p cnf {self.nv} {len(self.cl)}\n')
            for c in self.cl:
                f.write(' '.join(map(str, c)) + ' 0\n')


def completion_cnf(n1, n2, n3, alpha, beta, gamma, freeze, cards, lbmode='safe'):
    """CNF for the Brent equations with the slots in `freeze` fixed to the
    scheme's factors and the others free; cards is a set of
    {'entries','rank1','caps'}.  Returns (cnf, varmap) with varmap[(X, s, i, j)]."""
    r = alpha.shape[0]
    fac = {'a': alpha, 'b': beta, 'c': gamma}
    info = slot_info(n1, n2, n3)
    cnf = CNF()
    var = {}
    for X in 'abc':
        if X in freeze:
            continue
        h, w = info[X]['shape']
        for s in range(r):
            for i in range(h):
                for j in range(w):
                    var[(X, s, i, j)] = cnf.var()

    def lit(X, s, i, j):
        """literal or constant (True/False) for factor bit"""
        if X in freeze:
            return bool(fac[X][s, i, j])
        return var[(X, s, i, j)]

    # Brent equations: for all (i,k),(k',j),(i',j'): XOR_s a_s[ik] b_s[k'j] c_s[i'j'] = [k=k'][i=i'][j=j']
    for i in range(n1):
        for k in range(n2):
            for kk in range(n2):
                for j in range(n3):
                    for ii in range(n1):
                        for jj in range(n3):
                            rhs = (k == kk) and (i == ii) and (j == jj)
                            lits = []
                            const = False
                            for s in range(r):
                                fs = [lit('a', s, i, k), lit('b', s, kk, j), lit('c', s, ii, jj)]
                                if any(f is False for f in fs):
                                    continue
                                vs = [f for f in fs if f is not True]
                                if not vs:
                                    const ^= True
                                elif len(vs) == 1:
                                    lits.append(vs[0])
                                elif len(vs) == 2:
                                    lits.append(cnf.and2(vs[0], vs[1]))
                                else:
                                    lits.append(cnf.and2(cnf.and2(vs[0], vs[1]), vs[2]))
                            target = rhs ^ const
                            if not lits:
                                if target:
                                    cnf.add([])  # unsatisfiable
                                continue
                            y = cnf.xor_chain(lits)
                            cnf.add([y] if target else [-y])
    # capacity constraints on the free slots
    for X in 'abc':
        if X in freeze:
            continue
        h, w = info[X]['shape']
        m = info[X]['m']
        if 'entries' in cards:
            for i in range(h):
                for j in range(w):
                    cnf.at_least([var[(X, s, i, j)] for s in range(r)], m)
        if 'rank1' in cards:
            for uc in range(1, 1 << h):
                for vc in range(1, 1 << w):
                    cells = [(i, j) for i in range(h) if (uc >> i) & 1 for j in range(w) if (vc >> j) & 1]
                    if len(cells) == 1 and 'entries' in cards:
                        continue
                    lits = [cnf.xor_chain([var[(X, s, i, j)] for (i, j) in cells]) for s in range(r)]
                    cnf.at_least(lits, m)
        if 'caps' in cards:
            for kind, dim, q in (('row', h, info[X]['row_q']), ('col', w, info[X]['col_q'])):
                if min(q) < 1:
                    continue
                L, _ = lb(*q)
                cap = r - L
                for code in range(1, 1 << dim):
                    d = [(code >> t) & 1 for t in range(dim)]
                    zs = []
                    for s in range(r):
                        # condition: x_s in the direction's subspace
                        cond = []  # literals that must all be true
                        if kind == 'row':
                            first = next(k for k in range(h) if d[k])
                            for k in range(h):
                                for j in range(w):
                                    if not d[k]:
                                        cond.append(-var[(X, s, k, j)])
                                    elif k != first:
                                        e = cnf.var()  # e <-> (x_kj == x_firstj)
                                        x, y = var[(X, s, k, j)], var[(X, s, first, j)]
                                        cnf.add([-e, -x, y]); cnf.add([-e, x, -y]); cnf.add([e, x, y]); cnf.add([e, -x, -y])
                                        cond.append(e)
                        else:
                            first = next(j for j in range(w) if d[j])
                            for j in range(w):
                                for k in range(h):
                                    if not d[j]:
                                        cond.append(-var[(X, s, k, j)])
                                    elif j != first:
                                        e = cnf.var()
                                        x, y = var[(X, s, k, j)], var[(X, s, k, first)]
                                        cnf.add([-e, -x, y]); cnf.add([-e, x, -y]); cnf.add([e, x, y]); cnf.add([e, -x, -y])
                                        cond.append(e)
                        z = cnf.var()
                        cnf.add([z] + [-c for c in cond])  # cond -> z
                        zs.append(z)
                    cnf.at_most(zs, cap)
    return cnf, var


def run(path, timeout, seeds):
    rows = []
    for sd in seeds:
        t = time.time()
        p = subprocess.run([CADICAL, '-q', '-t', str(timeout), f'--seed={sd}', path], capture_output=True, text=True)
        el = time.time() - t
        st = 'SAT' if 's SATISFIABLE' in p.stdout else 'UNSAT' if 's UNSATISFIABLE' in p.stdout else 'UNKNOWN'
        rows.append((sd, st, el))
        print(f'{os.path.basename(path)} seed {sd}: {st} in {el:.2f} s')
    return rows


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('report'); p.add_argument('n1', type=int); p.add_argument('n2', type=int); p.add_argument('n3', type=int); p.add_argument('bits')
    p = sub.add_parser('lbtable')
    p = sub.add_parser('cnf'); p.add_argument('n1', type=int); p.add_argument('n2', type=int); p.add_argument('n3', type=int); p.add_argument('bits')
    p.add_argument('--freeze', default='a'); p.add_argument('--out', required=True); p.add_argument('--drop', type=int, default=None)
    p.add_argument('--card', default='')
    p = sub.add_parser('run'); p.add_argument('cnf'); p.add_argument('--timeout', type=int, default=600); p.add_argument('--seeds', default='1')
    a = ap.parse_args()
    if a.cmd == 'report':
        report(a.n1, a.n2, a.n3, a.bits)
    elif a.cmd == 'lbtable':
        for key in [(2, 2, 2), (2, 2, 3), (2, 2, 4), (2, 3, 3), (2, 3, 4), (2, 4, 4), (3, 3, 3), (3, 3, 4), (3, 4, 4), (4, 4, 4), (2, 3, 5), (3, 3, 5), (3, 4, 5), (4, 4, 5)]:
            v, prov = lb(*key)
            print(f'<{key[0]},{key[1]},{key[2]}> >= {v}   ({prov})')
    elif a.cmd == 'cnf':
        alpha, beta, gamma = load_bits(a.bits, a.n1, a.n2, a.n3)
        if a.drop is not None:
            keep = [s for s in range(alpha.shape[0]) if s != a.drop]
            alpha, beta, gamma = alpha[keep], beta[keep], gamma[keep]
        cards = set(x for x in a.card.split(',') if x)
        cnf, _ = completion_cnf(a.n1, a.n2, a.n3, alpha, beta, gamma, set(a.freeze), cards)
        cnf.write(a.out)
        print(f'{a.out}: <{a.n1},{a.n2},{a.n3}> r={alpha.shape[0]} freeze {a.freeze} card {sorted(cards)}: {cnf.nv} vars, {len(cnf.cl)} clauses')
    elif a.cmd == 'run':
        run(a.cnf, a.timeout, [int(x) for x in a.seeds.split(',')])


if __name__ == '__main__':
    main()
