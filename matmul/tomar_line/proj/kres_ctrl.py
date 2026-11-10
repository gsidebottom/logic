#!/usr/bin/env python3
"""Control schemes for the deficient-case decider of kres (src/bin/kres.rs).

  split P Q:  replace products P = a(x)b(x)c and Q = a'(x)b'(x)c' by the three products
                (a+a')(x)b(x)c,  a'(x)(b+b')(x)c,  a'(x)b'(x)(c+c')
              (same sum, and no Kronecker product repeats in any pairing).  P and Q are replaced in place and the third
              product is appended at index r, so a k-subset T containing P and Q becomes T + {r}: k+1 products with the
              same residual, hence reducible, and the same factor-span dimensions, hence a deficient candidate.
  flip [--pair P,Q]:  a Kauers-Moosbauer flip of two products sharing a factor (first such pair unless given):
                u(x)x(x)y + u(x)x'(x)y'  ->  u(x)(x+x')(x)y + u(x)x'(x)(y+y')      (u the shared factor, any slot)
              The mutant has the same residual on every subset containing P and Q, with the original pair as an
              alternative decomposition.
usage: kres_ctrl.py N1 N2 N3 scheme.bits split P Q out.bits
       kres_ctrl.py N1 N2 N3 scheme.bits flip out.bits [--pair P,Q]
"""
import sys, os, argparse
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from project_f2 import load_bits, check, to_bits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n1', type=int); ap.add_argument('n2', type=int); ap.add_argument('n3', type=int)
    ap.add_argument('bits'); ap.add_argument('op', choices=['split', 'flip']); ap.add_argument('rest', nargs='+')
    ap.add_argument('--pair')
    a = ap.parse_args()
    n1, n2, n3 = a.n1, a.n2, a.n3
    al, be, ga = load_bits(a.bits, n1, n2, n3); r = al.shape[0]
    assert check(al, be, ga, n1, n2, n3), 'input fails the tensor check'
    F = [al.copy(), be.copy(), ga.copy()]
    if a.op == 'split':
        p, q, out = int(a.rest[0]), int(a.rest[1]), a.rest[2]
        A, B, C = (F[s][p].copy() for s in range(3)); A2, B2, C2 = (F[s][q].copy() for s in range(3))
        new = [((A + A2) % 2, B, C), (A2, (B + B2) % 2, C), (A2, B2, (C + C2) % 2)]
        for s in range(3):
            F[s][p] = new[0][s]; F[s][q] = new[1][s]
            F[s] = np.concatenate([F[s], new[2][s][None]], axis=0)
        print(f'split {p},{q}: products {p} and {q} replaced in place, third appended at index {r}; rank {r + 1}')
    else:
        out = a.rest[0]
        pair = None
        if a.pair:
            p, q = map(int, a.pair.split(','))
            for s in range(3):
                if np.array_equal(F[s][p], F[s][q]):
                    pair = (p, q, s); break
            assert pair, 'the given pair shares no factor'
        else:
            for s in range(3):
                for p in range(r):
                    for q in range(p + 1, r):
                        if np.array_equal(F[s][p], F[s][q]):
                            pair = (p, q, s); break
                    if pair: break
                if pair: break
            assert pair, 'no two products share a factor'
        p, q, s = pair
        o = [t for t in range(3) if t != s]
        x, y = F[o[0]][p].copy(), F[o[1]][p].copy(); x2, y2 = F[o[0]][q].copy(), F[o[1]][q].copy()
        F[o[0]][p] = (x + x2) % 2; F[o[1]][p] = y
        F[o[0]][q] = x2;           F[o[1]][q] = (y + y2) % 2
        print(f'flip {p},{q} (shared slot {s}): both products replaced in place; rank {r}')
    assert check(F[0], F[1], F[2], n1, n2, n3), 'control scheme fails the tensor check'
    assert all(F[s][t].any() for s in range(3) for t in range(F[0].shape[0])), 'zero factor'
    open(out, 'w').write(to_bits(F[0], F[1], F[2]) + '\n')
    print(f'wrote {out}')


if __name__ == '__main__':
    main()
