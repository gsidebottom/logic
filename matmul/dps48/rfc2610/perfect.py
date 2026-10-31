#!/usr/bin/env python3
"""Build the frame-triple points of accurate_262 where 32 of the 64 stabilizer elements act by signed
permutations (frames.py), in all three role assignments, as exact dyadic schemes.  Each term's factors are
scaled by 1 or sqrt 2 to clear the frames' sqrt 2 (their product is rational), then by powers of two so
the most common magnitude in U and V is 1, and the remainder goes to P.  Exact Brent check on integers.

  perfect.py PREFIX FRAMES.json OUTDIR
"""
import json, os, sys
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
sys.path.insert(0, '/Users/greg/projects/logic/matmul/dps48/rfc2610'); sys.path.insert(0, '/Users/greg/projects/logic/matmul/dps48')
from collections import Counter
import itertools, re
import numpy as np
import gamma_fixed as GF
import orbit48 as O
src = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/frames.py').read()
exec(src[src.index('s = 2 ** -.5'):src.index('line = lambda')])
pre, fj, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)
U0, V0, W0 = GF.load(pre)     # cyclic reading: W0 is the transpose of P's column
triples = [t[1:] for t in json.load(open(fj)) if t[0] == 32]
def dy(M):
    "scale M by 1 or sqrt 2 so that its entries are dyadic; returns (scaled, scale)"
    for sc in (1.0, 2 ** .5):
        x = M * sc * 1024
        if np.abs(x - np.round(x)).max() < 1e-7: return M * sc, sc
    raise ValueError("not dyadic up to sqrt 2")
def mag(M):
    c = Counter(np.round(np.abs(M[np.abs(M) > 1e-9]), 8).tolist()); return c.most_common(1)[0][0]
E = np.zeros((4,) * 6, dtype=np.int64)
for a, b, c in itertools.product(range(4), repeat=3): E[a, b, b, c, a, c] = O.SCAL ** 3
rows = []
for a, b, c in triples:
    A, B, C = Fr_[a], Fr_[b], Fr_[c]
    Us, Vs, Ws = A @ U0 @ B.T, B @ V0 @ C.T, C @ W0 @ A.T
    for role in range(3):
        Ur, Vr, Wr = [(Us, Vs, Ws), (Vs, Ws, Us), (Ws, Us, Vs)][role]
        Un, Vn, Wn = [], [], []
        for k in range(48):
            u, su = dy(Ur[k]); v, sv = dy(Vr[k]); w = Wr[k] / (su * sv) * 1.0
            w0 = w / (su * sv) * 0 + Wr[k] * su * sv / 1.0  # placeholder keeps shapes
            mu, mv = mag(u), mag(v)
            u, v = u / mu, v / mv
            w = Wr[k] * (mu / su) * (mv / sv)  # u v w product unchanged: u_new v_new w_new = Ur Vr Wr
            Un.append(u); Vn.append(v); Wn.append(w)
        Un, Vn, Wn = np.array(Un), np.array(Vn), np.array(Wn)
        if np.abs(np.round(Wn * O.SCAL) - Wn * O.SCAL).max() > 1e-6: print("  non-dyadic P at", a, b, c, role); continue
        ui, vi, wi = (np.round(M * O.SCAL).astype(np.int64) for M in (Un, Vn, Wn.transpose(0, 2, 1)))
        ok = np.array_equal(np.einsum('kab,kcd,kef->abcdef', ui, vi, wi), E)
        _, floor, fs, nu = O.objective(ui, vi, wi, 0)
        nz = [int(np.count_nonzero(m)) for m in (ui, vi, wi)]
        can = [sum(1 for k in range(48) if np.count_nonzero(m[k]) == 1) for m in (ui, vi, wi)]
        tag = f"{re.sub(r'[^A-Za-z0-9]', '', a).replace('H', 'h')}{'p' if a == 'H+' else 'm' if a == 'H-' else ''}_{re.sub(r'[^A-Za-z0-9]', '', b)}{'p' if b == 'H+' else 'm' if b == 'H-' else ''}_{re.sub(r'[^A-Za-z0-9]', '', c)}{'p' if c == 'H+' else 'm' if c == 'H-' else ''}_r{role}"
        T = (Un, Vn, Wn)
        O.write_sms(f"{out}/{tag}", ui, vi, wi)
        rows.append(dict(tag=tag, brent=int(ok), floor=floor, fl=fs[0], fr=fs[1], fp=fs[2], nonunit=nu, nnz=sum(nz), can=can, g2=round(GF.gamma2(T), 4), ginf=round(GF.ginf(T), 4)))
        print(f"{tag:22s} Brent {int(ok)}  floors {fs} floor {floor}  nonunit {nu:4d}  nnz {nz} = {sum(nz)}  canon {can}  gamma_2 {GF.gamma2(T):.4f}  gamma_inf,2 {GF.ginf(T):.3f}")
json.dump(rows, open(f"{out}/score.json", "w"))
