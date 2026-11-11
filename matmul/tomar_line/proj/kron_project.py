#!/usr/bin/env python3
"""Project a matrix multiplication scheme to a smaller shape, exactly.

Prior art: restricting a scheme to a sub-shape is classical; the reduction that follows it here is the
2-reducibility of LITA (Khoruzhii, Serafin, Gelss, Pokutta, github.com/khoruzhii/lita), a generalisation
of the Kauers-Moosbauer reducibility.  This file only writes the restricted scheme.

A scheme for <n0, n1, n2> multiplies an n0 x n1 matrix A by an n1 x n2 matrix B.  Deleting an index of I
(rows of A), J (columns of A = rows of B) or K (columns of B) sets the matching entries to zero: the columns
of u (I x J), v (J x K) and w (K x I, the catalog's transposed result index k * n0 + i) are dropped and every
product with a zero factor disappears.  The result is a scheme for the smaller shape, in the catalog's JSON
layout with exact entries, ready for kron_reduce.py.

usage: kron_project.py SCHEME.json OUT.json [--I i,i,..] [--J j,..] [--K k,..]
"""
import sys, json

def cols_for(n, keep):
    n0, n1, n2 = n; I, J, K = keep
    return ([i * n1 + j for i in I for j in J], [j * n2 + k for j in J for k in K], [k * n0 + i for k in K for i in I])

def nonzero(x): return (x != 0) if not isinstance(x, str) else x.strip().lstrip('-+').split('/')[0].strip('0') != ''

if __name__ == '__main__':
    args = sys.argv[1:]; dels = [[], [], []]
    for s, flag in enumerate(('--I', '--J', '--K')):
        if flag in args:
            i = args.index(flag); dels[s] = sorted(int(x) for x in args[i + 1].split(',')); del args[i:i + 2]
    src, out = args
    d = json.load(open(src)); n = tuple(d['n']); m = d['m']
    assert len(d['u']) == len(d['v']) == len(d['w']) == m
    assert len(d['u'][0]) == n[0] * n[1] and len(d['v'][0]) == n[1] * n[2] and len(d['w'][0]) == n[2] * n[0]
    for s in range(3): assert all(0 <= i < n[s] for i in dels[s]) and len(set(dels[s])) == len(dels[s])
    keep = [[i for i in range(n[s]) if i not in dels[s]] for s in range(3)]
    cu, cv, cw = cols_for(n, keep)
    U = [[row[c] for c in cu] for row in d['u']]; V = [[row[c] for c in cv] for row in d['v']]; W = [[row[c] for c in cw] for row in d['w']]
    alive = [t for t in range(m) if any(nonzero(x) for x in U[t]) and any(nonzero(x) for x in V[t]) and any(nonzero(x) for x in W[t])]
    n2 = [len(k) for k in keep]
    json.dump({'n': n2, 'm': len(alive), 'z2': d.get('z2', False), 'u': [U[t] for t in alive], 'v': [V[t] for t in alive],
               'w': [W[t] for t in alive]}, open(out, 'w'))
    print(f'{src.split("/")[-1]}: {"x".join(map(str, n))} with {m} products; deleted I{dels[0]} J{dels[1]} K{dels[2]} -> '
          f'{"x".join(map(str, n2))} with {len(alive)} products; written {out}')
