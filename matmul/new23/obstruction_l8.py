#!/usr/bin/env python3
"""The alignment-vs-reduction obstruction experiment (4x4, L8 frontier).

For a sample of the banked level-8 beam states (rank 57), enumerate
one-slot-aligned pairs and solve the coincidence system
f_i(t) + lam*f_j(t) = mu*f_m(t) over EXACT RATIONALS with NO dyadic
restriction on lam.  Classify each solution:
  - conversion-enabling: the target m already shares another slot
    with i, so this flip would immediately allow the reduction (i,m)
    — i.e., a rank-56 event, blocked over Q only if lam is non-dyadic;
  - by lam type: dyadic (+-2^k — legal in flip48) vs non-dyadic
    rational (blocked by the engine's coefficient discipline).
Verdict logic: conversion-enabling solutions with non-dyadic lam
=> the obstruction is RATIONALITY (flip48 over F_p converts);
zero conversion-enabling solutions of any lam => the obstruction is
GEOMETRIC at these states."""
import sys
from fractions import Fraction

def pv(s):
    l, r = s.rsplit('], ', 1)
    return [int(x) for x in l.strip()[2:].split(',')], int(r.rstrip(') \n'))

def load_frontier(path):
    out = []
    for b in open(path).read().split('---\n'):
        if not b.strip():
            continue
        st = []
        for ln in b.strip().split('\n'):
            if ln.startswith('nearmiss'):
                continue
            st.append([pv(p) for p in ln.split(' | ')])
        if st:
            out.append(st)
    return out

def vec(f):
    nums, e = f
    m = Fraction(2) ** e
    return tuple(Fraction(x) * m for x in nums)

def prop(u, v):
    r = None
    for a, b in zip(u, v):
        if (a == 0) != (b == 0):
            return None
        if b != 0:
            q = a / b
            if r is None:
                r = q
            elif r != q:
                return None
    return r

def is_dyadic(fr):
    n, d = abs(fr.numerator), fr.denominator
    return n != 0 and (n & (n - 1)) == 0 and (d & (d - 1)) == 0

def analyze(st):
    n = len(st)
    V = [[vec(t[s]) for s in range(3)] for t in st]
    # shared/proportional pairs per slot
    shared = {}   # (i,j) -> set of slots where proportional
    for s in range(3):
        for i in range(n):
            for j in range(i + 1, n):
                if prop(V[i][s], V[j][s]) is not None:
                    shared.setdefault((i, j), set()).add(s)
    res = dict(pairs=0, sols=0, dy=0, nondy=0, conv_dy=0, conv_nondy=0)
    for (i, j), slots in shared.items():
        for s2 in slots:
            res['pairs'] += 1
            others = [t for t in range(3) if t != s2]
            for (oi, oj) in ((i, j), (j, i)):
                for t in others:
                    fi, fj = V[oi][t], V[oj][t]
                    for m in range(n):
                        if m == oi or m == oj:
                            continue
                        fm = V[m][t]
                        piv = None
                        for p in range(16):
                            for q in range(p + 1, 16):
                                det = fj[p] * (-fm[q]) - fj[q] * (-fm[p])
                                if det != 0:
                                    piv = (p, q, det)
                                    break
                            if piv:
                                break
                        if not piv:
                            continue
                        p, q, det = piv
                        nl = (-fi[p]) * (-fm[q]) - (-fi[q]) * (-fm[p])
                        nmu = fj[p] * (-fi[q]) - fj[q] * (-fi[p])
                        if nl == 0 or nmu == 0:
                            continue
                        lam = nl / det
                        if any(det * fi[x] + nl * fj[x] - nmu * fm[x] != 0
                               for x in range(16)):
                            continue
                        res['sols'] += 1
                        dy = is_dyadic(lam)
                        res['dy' if dy else 'nondy'] += 1
                        # conversion-enabling: oi and m already share a
                        # slot other than the transfer slot t
                        key = (min(oi, m), max(oi, m))
                        pre = shared.get(key, set()) - {t}
                        if pre:
                            res['conv_dy' if dy else 'conv_nondy'] += 1
    return res

if __name__ == '__main__':
    path = sys.argv[1] if len(sys.argv) > 1 else \
        'matmul/found48q/chase_frontier_L8.txt'
    step = int(sys.argv[2]) if len(sys.argv) > 2 else 15
    states = load_frontier(path)
    print(f'{len(states)} states loaded; sampling every {step}th',
          flush=True)
    tot = dict(pairs=0, sols=0, dy=0, nondy=0, conv_dy=0, conv_nondy=0)
    ns = 0
    for st in states[::step]:
        r = analyze(st)
        for k in tot:
            tot[k] += r[k]
        ns += 1
        if ns % 20 == 0:
            print(f'  [{ns} states] {tot}', flush=True)
    print(f'FINAL over {ns} states: {tot}', flush=True)
    print('interpretation: conv_nondy > 0 => rationality is the '
          'obstruction (F_p converts); conv_* all zero => geometric.',
          flush=True)
