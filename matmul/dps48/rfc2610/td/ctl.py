# Why is the (10,10) V-lines point worse than Joshua's L, R?  Compare rows up to scale and magnitudes.
import sys
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
from fractions import Fraction as Fr
from collections import Counter
import numpy as np
def sms(p):
    rows = [l.split() for l in open(p) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = np.zeros((r, c))
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1, int(t[1]) - 1] = float(Fr(t[2]))
    return M
SP = sys.argv[1]
pts = {"203": f"{SP}/rfc2610/files/4x4x4_48_203", "lam01c0": "/Users/greg/projects/logic/matmul/dps48/cand48/lam01c0_201", "b007": f"{SP}/td/vl/b007_10_10", "b069": f"{SP}/td/vl/b069_10_10"}
for n, p in pts.items():
    L, R = sms(p + "_L.sms"), sms(p + "_R.sms")
    f = lambda M: (int(np.count_nonzero(M)), Counter(np.round(np.abs(M[M != 0]), 4).tolist()).most_common(5))
    print(n, "L", f(L), "\n     R", f(R))
    print("     rows with mixed magnitudes: L", sum(1 for r in L if len(set(np.abs(r[r != 0]).tolist())) > 1), " R", sum(1 for r in R if len(set(np.abs(r[r != 0]).tolist())) > 1))
