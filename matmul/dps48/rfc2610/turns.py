#!/usr/bin/env python3
"""Growth factors of a rank-48 point in all six orientations, recomputed from the raw .sms and independent of
gamma48, for Sedoglavic's remark that the gamma_inf,2 search should be redone after turning the scheme.  Each
orientation is one of the six maps of s3_lrp.py on [L; R; P].  DPS's definition, the paper's eq. (gamma):
gamma_{p,q} = || ( sum_i ||L_i||_{q*} ||R_i||_{q*} |p_{j,i}| )_j ||_p, and gamma_2 = sum_i ||L_i||_2 ||R_i||_2 ||P_{*,i}||_2.

  turns.py DATA_DIR NAME [NAME ...]
"""
import itertools, math, sys
from fractions import Fraction as Fr
data, names = sys.argv[1], sys.argv[2:]

def read_sms(path):
    M = None
    for ln in open(path):
        p = ln.split()
        if M is None:
            if len(p) >= 2 and p[0].isdigit() and p[1].isdigit():
                M = [[0.0] * int(p[1]) for _ in range(int(p[0]))]
            continue
        if len(p) < 3 or (p[0] == "0" and p[1] == "0"):
            break
        M[int(p[0]) - 1][int(p[1]) - 1] = float(Fr(p[2]))
    return M
def tr(A): return [list(r) for r in zip(*A)]
def permcols(A, q): return [[r[q[j]] for j in range(len(r))] for r in A]
def permrows(A, q): return [A[q[i]] for i in range(len(A))]
Kp = [b * 4 + a for a in range(4) for b in range(4)]   # (K x)[a*4+b] = x[b*4+a]
def Rk(M): return permcols(M, Kp)    # M K
def Kl(M): return permrows(M, Kp)    # K M
MAPS = [("[L; R; P]", lambda L, R, P: (L, R, P)),
        ("[R K; L K; K P]", lambda L, R, P: (Rk(R), Rk(L), Kl(P))),
        ("[R; P^T K; K L^T]", lambda L, R, P: (R, Rk(tr(P)), Kl(tr(L)))),
        ("[P^T; R K; L^T]", lambda L, R, P: (tr(P), Rk(R), tr(L))),
        ("[L K; P^T; R^T]", lambda L, R, P: (Rk(L), tr(P), tr(R))),
        ("[P^T K; L; K R^T]", lambda L, R, P: (Rk(tr(P)), L, Kl(tr(R))))]
def n1(v): return sum(abs(x) for x in v)
def n2(v): return math.sqrt(sum(x * x for x in v))
def computes(L, R, P):
    bad = 0
    for i, j, l in itertools.product(range(16), repeat=3):
        v = sum(L[k][i] * R[k][j] * P[l][k] for k in range(48))
        bad += abs(v - (1 if i % 4 == j // 4 and l == (i // 4) * 4 + j % 4 else 0)) > 1e-9
    return bad
def gammas(L, R, P):
    w1 = [n1(a) * n1(b) for a, b in zip(L, R)]
    w2 = [n2(a) * n2(b) for a, b in zip(L, R)]
    s1 = [sum(w * abs(x) for w, x in zip(w1, row)) for row in P]
    s2 = [sum(w * abs(x) for w, x in zip(w2, row)) for row in P]
    Pc = tr(P)
    amp = max(0.5 * n2([w * x for w, x in zip(w2, row)]) for row in P)    # the paper's eq. (amp)
    return max(s1), max(s2), n2(s1), n2(s2), sum(w * n2(c) for w, c in zip(w2, Pc)), amp
print(f"{'point':14s} {'orientation':20s} {'g_inf,inf':>10s} {'g_inf,2':>10s} {'g_2,inf':>10s} {'g_2,2':>10s} {'g_2':>10s} {'amp':>10s}  Brent")
for name in names:
    L, R, P = (read_sms(f"{data}/4x4x4_48_{name}_{s}.sms") for s in "LRP")
    for m, f in MAPS:
        A = f(L, R, P)
        g = gammas(*A)
        print(f"{name:14s} {m:20s} " + " ".join(f"{x:10.4f}" for x in g) + f"  {computes(*A)}", flush=True)
