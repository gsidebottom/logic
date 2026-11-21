#!/usr/bin/env python3
"""Rewrite a scheme for <n0 x n1 x n2> as one of the same rank for the sorted format, by the symmetries of the
trilinear form trace(A B C') (catalog layout: u on A row-major, v on B row-major, w on C' = C transposed, row-major):

  rotation        trace(A B C') = trace(B C' A):   (u, v, w) -> (v, w, u), format (n1, n2, n0), no index change;
  transposition   trace(A B C') = trace(C'^T B^T A^T):  format (n0, n2, n1), each factor transposed:
                  u'[i n2 + k] = w[k n0 + i],  v'[k n1 + j] = v[j n2 + k],  w'[j n0 + i] = u[i n1 + j].

Entries are copied as they are (strings stay strings).  usage: scheme_orient.py IN.json[.gz] OUT.json.gz
Verify the output exactly afterwards (kron_verify.py)."""
import sys, json, gzip

def load(p):
    return json.load(gzip.open(p, 'rt') if p.endswith('.gz') else open(p))

def rotate(n, u, v, w):
    return [n[1], n[2], n[0]], v, w, u

def transpose(n, u, v, w):
    n0, n1, n2 = n
    tr = lambda rows, r, c: [[row[b * r + a] for a in range(r) for b in range(c)] for row in rows]
    # tr(rows, r, c): rows index a c x r matrix row-major (b r + a); the result indexes its r x c transpose (a c + b)
    return [n0, n2, n1], tr(w, n0, n2), tr(v, n2, n1), tr(u, n1, n0)

if __name__ == '__main__':
    d = load(sys.argv[1]); n, u, v, w = d['n'], d['u'], d['v'], d['w']; ops = []
    target = sorted(n)
    for plan in ([], ['r'], ['r', 'r'], ['t'], ['t', 'r'], ['t', 'r', 'r']):
        s = (list(n), u, v, w)
        for o in plan: s = rotate(*s) if o == 'r' else transpose(*s)
        if s[0] == target: break
    else:
        sys.exit('no ordering found')
    n2, u2, v2, w2 = s
    out = {'n': n2, 'm': d['m'], 'z2': d.get('z2', False), 'u': u2, 'v': v2, 'w': w2}
    with gzip.open(sys.argv[2], 'wt') as f: json.dump(out, f)
    print(f'{sys.argv[1].split("/")[-1]}: {n} -> {n2} by {"+".join({"r": "rotation", "t": "transposition"}[o] for o in plan) or "nothing"}; {d["m"]} products')
