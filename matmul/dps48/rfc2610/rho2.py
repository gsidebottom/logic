import sys, itertools
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
import numpy as np
from collections import Counter
from fractions import Fraction as Fr
def read_sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = np.zeros((r, c))
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1, int(t[1]) - 1] = float(Fr(t[2]))
    return M
def key(v):
    nz = v[np.abs(v) > 1e-9]; f = nz[0]; return tuple(np.round(v / f, 7) + 0.0), f
d3, d1 = sys.argv[1], sys.argv[2]
L3, R3, P3 = (read_sms(f"{d3}/4x4x4_48_203_{m}.sms") for m in "LRP")
targets = {n: tuple(read_sms(f"{d1}/4x4x4_48_{n}_{m}.sms") for m in "LRP") for n in ("201", "202")}
U = np.array([[0,1,0,0],[0,0,1,0],[0,0,0,1],[1,0,0,0]], float)
V = np.array([[0,0,1,0],[-1,-1,0,0],[1,0,0,0],[0,0,0,1]], float)
W = np.array([[0,-1,0,0],[0,0,1,0],[0,0,0,-1],[1,0,0,0]], float)
forms = {"": lambda M: M, "^-1": np.linalg.inv, "^T": lambda M: M.T, "^-T": lambda M: np.linalg.inv(M).T}
results = []
for (na, a), (nb, b), (nc, c) in itertools.permutations([("U", U), ("V", V), ("W", W)]):
    for fa, fb, fc in itertools.product(forms, repeat=3):
        A, B, C = forms[fa](a), forms[fb](b), forms[fc](c)
        Ai, Bi, Ci = map(np.linalg.inv, (A, B, C))
        L = L3 @ np.kron(Ai, B.T); R = R3 @ np.kron(Bi, C.T); P = np.kron(A, Ci.T) @ P3
        for tn, (L0, R0, P0) in targets.items():
            for sw in (False, True):
                X, Y = (R, L) if sw else (L, R)
                idx = {}
                for j in range(48): idx[(key(L0[j])[0], key(R0[j])[0])] = j
                hits = [(i, idx[(key(X[i])[0], key(Y[i])[0])]) for i in range(48) if (key(X[i])[0], key(Y[i])[0]) in idx]
                results.append((len(hits), tn, sw, f"{na}{fa},{nb}{fb},{nc}{fc}", hits, X, Y, P, L0, R0, P0))
results.sort(key=lambda t: -t[0])
print("best matches over 384 x 2 x 2 forms:", [(r[0], r[1], "swapped" if r[2] else "", r[3]) for r in results[:4]])
for n, tn, sw, name, hits, X, Y, P, L0, R0, P0 in results[:6]:
    if n == 48:
        c = Counter()
        for i, j in hits:
            a = key(X[i])[1] / key(L0[j])[1]; b = key(Y[i])[1] / key(R0[j])[1]
            cp = key(P[:, i])[1] / key(P0[:, j])[1] if key(P[:, i])[0] == key(P0[:, j])[0] else float('nan')
            c[(abs(a), abs(b), abs(cp))] += 1
        print(f"{tn} via {name}{' (L,R swapped)' if sw else ''}: (|L|, |R|, |P|) scalars, 203 image over target:")
        for k, v in sorted(c.items(), key=lambda t: -t[1]): print("   ", tuple(round(x, 4) for x in k), v)
        break
