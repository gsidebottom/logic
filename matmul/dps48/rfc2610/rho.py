# Apply rho (eq. 5 of RFC 2610) by Lemma 2.1 to the 203 point and compare with our 201 point, exactly.
import sys
from fractions import Fraction as Fr
from collections import Counter
def read_sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = [[Fr(0)] * c for _ in range(r)]
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1][int(t[1]) - 1] = Fr(t[2])
    return M
def mul(A, B):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(row, col) if a and b) for col in Bt] for row in A]
def T(M): return [list(c) for c in zip(*M)]
def kron(A, B): return [[a * b for a in ra for b in rb] for ra in A for rb in B]
def inv(M):
    n = len(M); A = [list(map(Fr, r)) + [Fr(i == j) for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0); A[c], A[p] = A[p], A[c]
        A[c] = [x / A[c][c] for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0: A[r] = [x - A[r][c] * y for x, y in zip(A[r], A[c])]
    return [r[n:] for r in A]
def brent(L, R, P):
    return sum(sum(P[a*4+c2][i] * L[i][a2*4+b] * R[i][b2*4+c] for i in range(48)) != (a == a2 and b == b2 and c == c2)
               for a in range(4) for b in range(4) for c in range(4) for a2 in range(4) for b2 in range(4) for c2 in range(4))
def act(L, R, P, U, V, W):
    Ui, Vi, Wi = inv(U), inv(V), inv(W)
    return mul(L, kron(Ui, T(V))), mul(R, kron(Vi, T(W))), mul(kron(U, T(Wi)), P)
def norm(v):
    f = next(x for x in v if x != 0); return tuple(x / f for x in v), f
def compare(L, R, P, L0, R0, P0, label):
    idx = {}
    for i, row in enumerate(L0):
        for j, r2 in enumerate(R0):
            pass
    keyL = {}
    for i in range(48): keyL.setdefault((norm(L0[i])[0], norm(R0[i])[0]), i)
    res = []
    Pc, P0c = T(P), T(P0)
    for i in range(48):
        k = (norm(L[i])[0], norm(R[i])[0])
        if k in keyL:
            j = keyL[k]; a = norm(L[i])[1] / norm(L0[j])[1]; b = norm(R[i])[1] / norm(R0[j])[1]
            c = norm(Pc[i])[1] / norm(P0c[j])[1] if norm(Pc[i])[0] == norm(P0c[j])[0] else None
            res.append((abs(a), abs(b), None if c is None else abs(c)))
    print(f"{label}: {len(res)}/48 products match; (|L ratio|, |R ratio|, |P ratio|) counts:")
    for t, n in Counter(res).most_common():
        print("    ", tuple(str(x) for x in t), n)
d3, d1 = sys.argv[1], sys.argv[2]
L3, R3, P3 = (read_sms(f"{d3}/4x4x4_48_203_{m}.sms") for m in "LRP")
L1, R1, P1 = (read_sms(f"{d1}/4x4x4_48_201_{m}.sms") for m in "LRP")
U = [[0,1,0,0],[0,0,1,0],[0,0,0,1],[1,0,0,0]]
V = [[0,0,1,0],[-1,-1,0,0],[1,0,0,0],[0,0,0,1]]
W = [[0,-1,0,0],[0,0,1,0],[0,0,0,-1],[1,0,0,0]]
for name, (a, b, c) in {"rho": (U, V, W), "rho^-1": (inv(U), inv(V), inv(W))}.items():
    La, Ra, Pa = act(L3, R3, P3, a, b, c)
    print(f"{name} on the 203 point: Brent violated {brent(La, Ra, Pa)} of 4096")
    compare(La, Ra, Pa, L1, R1, P1, f"  {name}(203) vs our 201")
    compare(Ra, La, Pa, L1, R1, P1, f"  {name}(203) with L,R swapped vs our 201")
print("U kron W^-T is a signed permutation:", all(sum(1 for x in r if x) == 1 and abs(next(x for x in r if x)) == 1 for r in kron(U, T(inv(W)))))
