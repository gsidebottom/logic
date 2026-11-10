#!/usr/bin/env python3
"""Exact stage of the k-subset re-solve without SAT, by slice spaces (candidates from src/bin/kres.rs).

R = the sum of the k dropped products, restricted to its three factor spans.  Its rank is at least each flattening rank
r_a, r_b, r_c (the dimensions of the three slice spaces S_a, S_b, S_c).  If rank(R) = r_a =: m then R = sum_{s<=m}
x_s (x) Y_s with the x_s a basis of the image, so the slices of R in the dual basis are the Y_s, of rank <= 1: the
slice space S_a is spanned by its rank-one elements; conversely a basis of S_a of rank-one matrices Y'_s gives
R = sum x'_s (x) Y'_s with m terms.  Hence
  reduce : if some flattening rank equals k-1, rank(R) <= k-1 iff that slice space (2^(k-1)-1 elements) is spanned by
           its rank-one elements -- exact, microseconds; the (k-1)-term decomposition is rebuilt into a scheme of rank
           r-1, Brent-checked and written.  If every flattening rank is <= k-2 the candidate is written to the SAT list.
  alt    : if some flattening rank equals k, the k-term decompositions of R are exactly the bases of that slice space
           made of rank-one elements; every basis other than the original is rebuilt into a scheme of rank r (no flip
           reaches it), Brent-checked, deduplicated, written.  If no flattening rank equals k (all three slots
           dependent), the candidate goes to the SAT list.
usage: kres_exact.py N1 N2 N3 scheme.bits candidates.txt --mode reduce|alt --out DIR [--tag T] [--kmax K]
       [--max-alts 50] [--quiet]
"""
import sys, os, re, time, argparse, itertools
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from project_f2 import load_bits, check, to_bits


def vec_of(bits):
    return int(''.join(str(int(b)) for b in bits), 2)


def basis_and_coords(rows):
    basis = []; ech = []
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
    return basis, [table[r] for r in rows]


def f2_rank(rows):
    """rank of a list of ints as F2 vectors"""
    ech = []
    for r in rows:
        x = r
        for e in ech:
            if x ^ e < x:
                x ^= e
        if x:
            ech.append(x); ech.sort(reverse=True)
    return len(ech)


def mat_rank(M, nrows, ncols):
    """M: int bitmask of an nrows x ncols matrix (row-major, bit (i*ncols+j)); rank over F2"""
    rows = [(M >> (i * ncols)) & ((1 << ncols) - 1) for i in range(nrows)]
    return f2_rank(rows)


def rank1_factors(M, nrows, ncols):
    """for a rank-1 matrix bitmask return (y, z) ints with M = y z^T"""
    rows = [(M >> (i * ncols)) & ((1 << ncols) - 1) for i in range(nrows)]
    z = next(r for r in rows if r)
    y = sum(1 << i for i, r in enumerate(rows) if r)
    assert all(r == 0 or r == z for r in rows)
    return y, z


class Cand:
    """R in coordinates: alpha[t], beta[t], gamma[t] are ints over da, db, dc bits (bit j = coordinate j)."""
    def __init__(self, al, be, ga, dims):
        self.al, self.be, self.ga = al, be, ga
        self.dims = dims
        self.k = len(al)

    def slices(self, direction):
        """direction 0: slices along a (indexed by a-coordinate u), each a db x dc matrix bitmask (bit v*dc+w);
        1: along b (v) -> da x dc (bit u*dc+w); 2: along c (w) -> da x db (bit u*db+v).  Returns (list of masks, nrows, ncols)."""
        da, db, dc = self.dims
        if direction == 0:
            n, nr, nc = da, db, dc
            F, G, H = self.al, self.be, self.ga
        elif direction == 1:
            n, nr, nc = db, da, dc
            F, G, H = self.be, self.al, self.ga
        else:
            n, nr, nc = dc, da, db
            F, G, H = self.ga, self.al, self.be
        out = []
        for i in range(n):
            M = 0
            for t in range(self.k):
                if (F[t] >> i) & 1:
                    # add G[t] (x) H[t] as a matrix
                    g, h = G[t], H[t]
                    for p in range(nr):
                        if (g >> p) & 1:
                            M ^= h << (p * nc)
            out.append(M)
        return out, nr, nc


def span_elements(basis):
    """all nonzero elements of the span of a list of ints, each with its coefficient mask"""
    d = len(basis); out = []
    for c in range(1, 1 << d):
        v = 0
        for j in range(d):
            if (c >> j) & 1:
                v ^= basis[j]
        out.append((v, c))
    return out


def rank1_bases(slices, nr, nc, m, exclude=None, max_bases=50):
    """Slice space S = span(slices) of dimension m.  Return the bases of S made of rank-1 elements, as lists of
    (matrix, y, z); `exclude` is a set of frozensets of matrices to skip (the original decomposition)."""
    sb = []; ech = []
    for s in slices:
        x = s
        for e in ech:
            if x ^ e < x:
                x ^= e
        if x:
            sb.append(s); ech.append(x); ech.sort(reverse=True)
    assert len(sb) == m
    r1 = [v for v, _ in span_elements(sb) if mat_rank(v, nr, nc) == 1]
    if f2_rank(r1) < m:
        return [], len(r1)
    bases = []
    for combo in itertools.combinations(r1, m):
        if f2_rank(list(combo)) == m:
            fs = frozenset(combo)
            if exclude is not None and fs in exclude:
                continue
            bases.append([(v,) + rank1_factors(v, nr, nc) for v in combo])
            if len(bases) >= max_bases:
                break
    return bases, len(r1)


def rebuild(cand, direction, basis_terms, sl, nr, nc):
    """From a rank-1 basis of the slice space in `direction`, the terms x'_s (x) y'_s (x) z'_s in coordinates:
    x'_s has coordinate i = coefficient of basis element s in slice i."""
    mats = [b[0] for b in basis_terms]; m = len(mats)
    # express each slice in the basis: brute force over 2^m combinations
    table = {}
    for c in range(1 << m):
        v = 0
        for j in range(m):
            if (c >> j) & 1:
                v ^= mats[j]
        table[v] = c
    xs = [0] * m
    for i, s in enumerate(sl):
        c = table[s]
        for j in range(m):
            if (c >> j) & 1:
                xs[j] |= 1 << i
    terms = []
    for j in range(m):
        _, y, z = basis_terms[j]
        if direction == 0:
            terms.append((xs[j], y, z))      # (a, b, c) coordinates
        elif direction == 1:
            terms.append((y, xs[j], z))      # slices along b: matrix rows = a, cols = c
        else:
            terms.append((y, z, xs[j]))      # slices along c: matrix rows = a, cols = b
    return terms


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n1', type=int); ap.add_argument('n2', type=int); ap.add_argument('n3', type=int)
    ap.add_argument('bits'); ap.add_argument('cands')
    ap.add_argument('--mode', choices=['reduce', 'alt'], required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--tag', default='k'); ap.add_argument('--kmax', type=int, default=99)
    ap.add_argument('--max-alts', type=int, default=50); ap.add_argument('--quiet', action='store_true')
    a = ap.parse_args()
    n1, n2, n3 = a.n1, a.n2, a.n3
    al, be, ga = load_bits(a.bits, n1, n2, n3); r = al.shape[0]
    assert check(al, be, ga, n1, n2, n3), 'input fails the tensor check'
    A = [vec_of(al[t].reshape(-1)) for t in range(r)]; B = [vec_of(be[t].reshape(-1)) for t in range(r)]; C = [vec_of(ga[t].reshape(-1)) for t in range(r)]
    wa, wb, wc = n1 * n2, n2 * n3, n1 * n3
    os.makedirs(a.out, exist_ok=True)
    sat_list = open(os.path.join(a.out, f'{a.tag}_{a.mode}_needs_sat.txt'), 'w')
    orig_key = tuple(sorted(zip(A, B, C)))
    found = {}; stats = {'decided_no': 0, 'reduced': 0, 'alts': 0, 'unique': 0, 'needs_sat': 0, 'bug': 0}
    t0 = time.time(); done = 0
    def tobits(v, w):
        return np.array([(v >> (w - 1 - j)) & 1 for j in range(w)], dtype=np.uint8)
    def emit(prods, line, label):
        cnt = {}
        for p in prods: cnt[p] = cnt.get(p, 0) + 1
        prods = [p for p, c in cnt.items() if c % 2 == 1]
        rk = len(prods)
        al2 = np.array([tobits(p[0], wa) for p in prods]).reshape(rk, n1, n2)
        be2 = np.array([tobits(p[1], wb) for p in prods]).reshape(rk, n2, n3)
        ga2 = np.array([tobits(p[2], wc) for p in prods]).reshape(rk, n1, n3)
        if not check(al2, be2, ga2, n1, n2, n3):
            stats['bug'] += 1; print(f'  BUG: rebuilt scheme fails the tensor check: {line.strip()}'); return
        key = tuple(sorted(prods))
        if key == orig_key or key in found:
            return
        name = f'{a.tag}_{label}_r{rk}_{len(found):05d}.bits'
        open(os.path.join(a.out, name), 'w').write(to_bits(al2, be2, ga2) + '\n'); found[key] = name
        if rk < r:
            print('!' * 60); print(f'RANK {rk} < {r}: {name} from candidate {line.strip()}'); print('!' * 60, flush=True)
        elif not a.quiet:
            print(f'  alt rank {rk}: {name} from {line.strip()}')
    for line in open(a.cands):
        if line[0] not in 'RA':
            continue
        m = re.match(r'([RA]) k=(\d+) dims=(\d+),(\d+),(\d+) idx=([\d,]+)', line)
        k = int(m.group(2))
        if k > a.kmax:
            continue
        if a.mode == 'reduce' and m.group(1) != 'R':
            continue
        idx = [int(x) for x in m.group(6).split(',')]
        ba, ca = basis_and_coords([A[i] for i in idx]); bb, cb = basis_and_coords([B[i] for i in idx]); bc, cc = basis_and_coords([C[i] for i in idx])
        cand = Cand(ca, cb, cc, (len(ba), len(bb), len(bc)))
        bases_amb = (ba, bb, bc)
        target = k - 1 if a.mode == 'reduce' else k
        decided = False
        for direction in range(3):
            sl, nr, nc = cand.slices(direction)
            rk_flat = f2_rank(sl)
            if rk_flat != target:
                continue
            exclude = None
            if a.mode == 'alt':
                # the original decomposition's slice-basis: Y_t = the k slice-space elements b_t c_t^T (direction 0),
                # or the analogous matrices for the other directions
                if direction == 0:
                    orig = [sum((cand.ga[t] << (p * nc)) for p in range(nr) if (cand.be[t] >> p) & 1) for t in range(k)]
                elif direction == 1:
                    orig = [sum((cand.ga[t] << (p * nc)) for p in range(nr) if (cand.al[t] >> p) & 1) for t in range(k)]
                else:
                    orig = [sum((cand.be[t] << (p * nc)) for p in range(nr) if (cand.al[t] >> p) & 1) for t in range(k)]
                exclude = {frozenset(orig)}
            bases, nr1 = rank1_bases(sl, nr, nc, target, exclude=exclude, max_bases=a.max_alts)
            decided = True
            if not bases:
                stats['decided_no' if a.mode == 'reduce' else 'unique'] += 1
                break
            keep = [t for t in range(r) if t not in set(idx)]
            for bt in bases:
                terms = rebuild(cand, direction, bt, sl, nr, nc)
                new = []
                for (xa, yb, zc) in terms:
                    av = 0; bv = 0; cv = 0
                    for j in range(len(ba)):
                        if (xa >> j) & 1: av ^= ba[j]
                    for j in range(len(bb)):
                        if (yb >> j) & 1: bv ^= bb[j]
                    for j in range(len(bc)):
                        if (zc >> j) & 1: cv ^= bc[j]
                    if av and bv and cv:
                        new.append((av, bv, cv))
                prods = [(A[t], B[t], C[t]) for t in keep] + new
                emit(prods, line, 'red' if a.mode == 'reduce' else 'alt')
                stats['reduced' if a.mode == 'reduce' else 'alts'] += 1
            break
        if not decided:
            stats['needs_sat'] += 1; sat_list.write(line)
        done += 1
        if not a.quiet and done % 20000 == 0:
            print(f'c {done} candidates, {stats}, {time.time() - t0:.0f} s', flush=True)
    sat_list.close()
    print(f'c done: {done} candidates, {stats}, {len(found)} distinct schemes written to {a.out}, {time.time() - t0:.0f} s')


if __name__ == '__main__':
    main()
