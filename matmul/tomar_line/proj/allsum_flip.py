#!/usr/bin/env python3
"""All-sum translation of an F2 scheme.
(Prior art: the move is the block flip of LITA -- K. Khoruzhii, L. Serafin, P. Gelss, S. Pokutta, "Local
Improvements to Trilinear Aggregation", github.com/khoruzhii/lita: a rank-one element u' (x) v' of the span of the
pair factors X_t = u_t (x) v_t replaces one of them.  "All-sum" is the case where it is the sum of all X_t.)

If the Kronecker products of two slots summed over ALL products give a rank-one matrix x (x) y
(direction d = the third slot), then for every vector beta of slot d
    T = sum_t a_t (x) (b_t + beta) (x) c_t  +  x (x) beta (x) y        (written for d = the b slot)
and beta = b_j kills product j: a scheme of the same rank sharing no product with the original.
usage: allsum_flip.py N scheme.bits [--out DIR --tag TAG]
Prints the rank of the all-sum in the three directions; with --out writes the r neighbours of every
direction whose all-sum is rank one, each verified against the tensor of the original.
"""
import sys, os

def load(path, w):
    bits = open(path).read().split()[-1]
    per = 3 * w
    assert len(bits) % per == 0
    r = len(bits) // per
    return [[int(bits[s * r * w + m * w: s * r * w + (m + 1) * w][::-1], 2) for s in range(3)] for m in range(r)]

def dump(prods, w):
    return ''.join(''.join(format(p[s], f'0{w}b')[::-1] for p in prods) for s in range(3))

def tensor(prods, w):
    t = {}
    for a, b, c in prods:
        for i in range(w):
            if (a >> i) & 1:
                for j in range(w):
                    if (b >> j) & 1:
                        key = i * w + j
                        t[key] = t.get(key, 0) ^ c
    return {k: v for k, v in t.items() if v}

def rank_rows(rows):
    piv = {}
    for v in rows:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; break
    return len(piv)

def allsum(prods, d, w):
    r, c = [(1, 2), (0, 2), (0, 1)][d]
    rows = [0] * w
    for p in prods:
        for i in range(w):
            if (p[r] >> i) & 1:
                rows[i] ^= p[c]
    return rows

if __name__ == '__main__':
    n = int(sys.argv[1]); w = n * n
    path = sys.argv[2]
    out = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
    tag = sys.argv[sys.argv.index('--tag') + 1] if '--tag' in sys.argv else os.path.basename(path).replace('.bits', '')
    prods = load(path, w)
    T = tensor(prods, w)
    ranks = []
    for d in range(3):
        rows = allsum(prods, d, w)
        rk = rank_rows(rows)
        ranks.append(rk)
        if rk != 1 or out is None:
            continue
        r, c = [(1, 2), (0, 2), (0, 1)][d]
        y = next(v for v in rows if v)
        x = sum(1 << i for i in range(w) if rows[i])
        assert all(v in (0, y) for v in rows)
        os.makedirs(out, exist_ok=True)
        nwritten = 0
        for j in range(len(prods)):
            beta = prods[j][d]
            new = []
            for t, p in enumerate(prods):
                if t == j: continue
                q = list(p); q[d] ^= beta
                assert q[d] != 0, 'two products share a factor'
                new.append(q)
            q = [0, 0, 0]; q[r] = x; q[c] = y; q[d] = beta
            new.append(q)
            assert tensor(new, w) == T, 'neighbour is not a scheme of the same tensor'
            assert len(set(map(tuple, new))) == len(new)
            with open(os.path.join(out, f'{tag}_d{d}_j{j:02d}.bits'), 'w') as f:
                f.write(dump(new, w) + '\n')
            nwritten += 1
        print(f'{tag}: direction {d}: wrote {nwritten} neighbours (each verified against the original tensor) to {out}')
    print(f'{tag}: {len(prods)} products, all-sum ranks by direction {ranks}')
