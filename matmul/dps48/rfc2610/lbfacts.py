# Orbit-invariant facts about the 201 record, to judge which lower-bound method could reach it.
import sys, re, itertools
from fractions import Fraction as F
import numpy as np
D = sys.argv[1]
def sms(path):
    toks = open(path).read().split()
    m, n = int(toks[0]), int(toks[1])
    M = np.zeros((m, n))
    i = 3
    while i + 2 < len(toks):
        r, c, v = int(toks[i]), int(toks[i+1]), toks[i+2]
        i += 3
        if r == 0: break
        M[r-1, c-1] = float(F(v))
    return M
def slpcount(path):
    add = sc = 0
    for line in open(path):
        line = line.strip().rstrip(';')
        if ':=' not in line: continue
        rhs = line.split(':=')[1].strip()
        body = rhs[1:] if rhs[:1] == '-' else rhs
        plus = len(re.findall(r'[+-]', body))
        add += plus
        sc += len(re.findall(r'[*/]', rhs))
    return add, sc
for side in 'LRP':
    M = sms(f'{D}/p005_201n_{side}.sms')
    if side == 'P': M = M.T
    assert M.shape == (48, 16), M.shape
    wt = (np.abs(M) > 1e-9).sum(1)
    unit = M / np.array([r[np.flatnonzero(np.abs(r) > 1e-9)[0]] for r in M])[:, None]
    lines = {tuple(np.round(r, 6)) for r in unit}
    ranks = [np.linalg.matrix_rank(r.reshape(4, 4), tol=1e-9) for r in M]
    # collinear triples of output lines (orbit invariant)
    idx = np.array(list(itertools.combinations(range(48), 3)))
    S = np.linalg.svd(M[idx], compute_uv=False)
    t3 = int((S[:, 2] < 1e-9).sum())
    idx4 = np.array(list(itertools.combinations(range(48), 4)))
    S4 = np.linalg.svd(M[idx4], compute_uv=False)
    t4 = int((S4[:, 3] < 1e-9).sum()) 
    print(f'{side}: nnz {int(wt.sum())}, canonical rows {int((wt==1).sum())}, distinct lines {len(lines)}, floor {len(lines)-int((wt==1).sum())}, '
          f'rank histogram { {r: ranks.count(r) for r in sorted(set(ranks))} }, collinear triples {t3}, dependent 4-sets {t4}')
for name in ['p005_201n_L','p005_201n_R','p005_201n_P']:
    print(name, 'adds, scalings by a crude count:', slpcount(f'{D}/{name}.slp'))
