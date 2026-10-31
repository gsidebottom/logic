import sys, itertools
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
from fractions import Fraction
import numpy as np
def read_sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = [[Fraction(0)] * c for _ in range(r)]
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1][int(t[1]) - 1] = Fraction(t[2])
    return M
def brent(L, R, P, g1=4, g2=4, g3=4):
    # vec(AB) = P ((L vecA) o (R vecB)), row-major: sum_i P[(a g3 + c), i] L[i, a g2 + b] R[i, b g3 + c'] = [c == c'] for all a,b,c,c' and other index combos
    r = len(L); bad = 0
    for a in range(g1):
        for b in range(g2):
            for c in range(g3):
                for a2 in range(g1):
                    for b2 in range(g2):
                        for c2 in range(g3):
                            s = sum(P[a * g3 + c2][i] * L[i][a2 * g2 + b] * R[i][b2 * g3 + c] for i in range(r))
                            want = 1 if (a == a2 and b == b2 and c == c2) else 0
                            bad += (s != want)
    return bad
def canon(M):
    return sum(1 for row in M if sum(1 for x in row if x != 0) == 1 and abs([x for x in row if x != 0][0]) == 1)
def measures(L, R, P):
    L = np.array([[float(x) for x in row] for row in L]); R = np.array([[float(x) for x in row] for row in R]); P = np.array([[float(x) for x in row] for row in P])
    l2 = np.linalg.norm(L, axis=1); r2 = np.linalg.norm(R, axis=1)
    amp = (0.5 * np.sqrt((P ** 2) @ (l2 ** 2 * r2 ** 2))).max(); ginf = (np.abs(P) @ (l2 * r2)).max()
    return amp, ginf
for name, pre in [("203 (Alexandre)", sys.argv[1] + "/4x4x4_48_203_"), ("201 (ours)", sys.argv[2] + "/4x4x4_48_201_"), ("accurate_262 (DPS)", sys.argv[2] + "/4x4x4_48_accurate_262_")]:
    L, R, P = (read_sms(pre + m + ".sms") for m in "LRP")
    bad = brent(L, R, P)
    amp, ginf = measures(L, R, P)
    nz = tuple(sum(1 for row in M for x in row if x != 0) for M in (L, R, P))
    print(f"{name}: Brent equations violated {bad} of 4096; canonical rows L {canon(L)}, R {canon(R)}, P columns {canon([list(c) for c in zip(*P)])}; nonzeros L/R/P {nz}; amp {amp:.3f}, gamma_inf2 {ginf:.3f}")
