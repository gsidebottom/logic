"""Question 3 (Sedoglavic, 2026-11-09): the invariant subspaces of R^4 under the stabilizer of a rank-48 point,
per mode, exactly over Q; the change of basis adapted to them; the decomposition in that basis; and how many
terms then become Kronecker products of 2x2 matrices (a doubled smaller scheme, as Laderman is of Strassen).
usage: q3_invariant.py PREFIX STAB.json    (STAB.json from rfc2610/stab_matrices.py on PREFIX)"""
import sys, json, random
from fractions import Fraction as Fr
from collections import Counter
pre, stab = sys.argv[1:3]
def read_sms(p):
    rows = [l.split() for l in open(p) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = [[Fr(0)] * c for _ in range(r)]
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1][int(t[1]) - 1] = Fr(t[2])
    return M
L, R, P = (read_sms(f"{pre}_{m}.sms") for m in "LRP")
U = [[[L[k][4*i+j] for j in range(4)] for i in range(4)] for k in range(48)]
V = [[[R[k][4*i+j] for j in range(4)] for i in range(4)] for k in range(48)]
Wc = [[[P[4*i+j][k] for j in range(4)] for i in range(4)] for k in range(48)]   # column k of P as 4x4 (c_ij)
def T(M): return [[M[j][i] for j in range(4)] for i in range(4)]
def mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def inv(M):
    n = 4; A = [row[:] + [Fr(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0); A[c], A[p] = A[p], A[c]
        f = A[c][c]; A[c] = [x / f for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                g = A[i][c]; A[i] = [x - g * y for x, y in zip(A[i], A[c])]
    return [row[n:] for row in A]
def ip(A, B): return sum(A[i][j] * B[i][j] for i in range(4) for j in range(4))
def tr3(A, B, C): return sum(mm(mm(A, B), C)[i][i] for i in range(4))
rnd = random.Random(5)
def rmat(): return [[Fr(rnd.randint(-3, 3)) for _ in range(4)] for _ in range(4)]
def cyclic_ok(U, V, W):
    "the cyclic reading: sum_k <U_k,A><V_k,B><W_k,C> = Tr(A B C) for all A, B, C"
    for _ in range(4):
        A, B, C = rmat(), rmat(), rmat()
        if sum(ip(U[k], A) * ip(V[k], B) * ip(W[k], C) for k in range(48)) != tr3(A, B, C): return False
    return True
W = [T(M) for M in Wc]
if not cyclic_ok(U, V, W):
    W = Wc
    assert cyclic_ok(U, V, W), "neither W nor W^T gives the cyclic trace form"
    print("cyclic reading uses W = P column as is")
else:
    print("cyclic reading uses W = (P column)^T, as stab_matrices.py does")
el = json.load(open(stab)); triv = [e for e in el if e['slot'] == 'id']
print(f"{len(el)} stabilizer elements, {len(triv)} with trivial slot map; slot maps {dict(Counter(e['slot'] for e in el))}")
def tomat(m): return [[Fr(str(x)) for x in row] for row in m]
# exact commutant per mode: all M with g M = M g for every trivial-slot element g of that mode
def nullspace(rows, nvar):
    A = [r[:] for r in rows]; piv = []; rnk = 0
    for c in range(nvar):
        p = next((i for i in range(rnk, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[rnk], A[p] = A[p], A[rnk]; f = A[rnk][c]; A[rnk] = [x / f for x in A[rnk]]
        for i in range(len(A)):
            if i != rnk and A[i][c] != 0:
                g = A[i][c]; A[i] = [x - g * y for x, y in zip(A[i], A[rnk])]
        piv.append(c); rnk += 1
    free = [c for c in range(nvar) if c not in piv]; basis = []
    for fcol in free:
        v = [Fr(0)] * nvar; v[fcol] = Fr(1)
        for i, pc in enumerate(piv): v[pc] = -A[i][fcol]
        basis.append(v)
    return basis
def charpoly_roots(J):
    "rational eigenvalues of a 4x4 rational matrix, by the rational root test on det(J - x I) via Fraction-free evaluation"
    # characteristic polynomial coefficients by Faddeev-LeVerrier
    n = 4; c = [Fr(0)] * (n + 1); c[n] = Fr(1); Mk = [[Fr(0)] * n for _ in range(n)]
    for k in range(1, n + 1):
        Mk = mm(J, Mk); 
        for i in range(n): Mk[i][i] += c[n - k + 1]
        c[n - k] = -sum(mm(J, Mk)[i][i] for i in range(n)) / k
    # p(x) = sum c[i] x^i ; rational roots among divisors (scaled)
    den = 1
    for x in c: den = den * x.denominator // __import__('math').gcd(den, x.denominator)
    ic = [int(x * den) for x in c]
    a0, an = ic[0], ic[n]
    roots = set()
    if a0 == 0: roots.add(Fr(0))
    def divisors(m):
        m = abs(m); out = set()
        for d in range(1, int(m ** .5) + 1):
            if m % d == 0: out |= {d, m // d}
        return out or {1}
    for p in divisors(a0 if a0 else 1):
        for q in divisors(an):
            for s in (1, -1):
                x = Fr(s * p, q)
                if sum(ic[i] * x ** i for i in range(n + 1)) == 0: roots.add(x)
    return c, sorted(roots)
bases = {}
for n in "XYZ":
    G = [tomat(e[n]) for e in triv]
    eqs = []
    for g in G:
        for i in range(4):
            for j in range(4):
                row = [Fr(0)] * 16
                for k in range(4):
                    row[i * 4 + k] += -g[k][j]       # -(M g)[i][j] contribution M[i][k] g[k][j]
                    row[k * 4 + j] += g[i][k]        # (g M)[i][j] contribution g[i][k] M[k][j]
                eqs.append(row)
    comm = nullspace(eqs, 16)
    print(f"mode {n}: commutant of the {len(G)} trivial-slot matrices has dimension {len(comm)}")
    J = [[sum((idx + 1) * (3 if idx % 2 else 1) * b[i * 4 + j] for idx, b in enumerate(comm)) for j in range(4)] for i in range(4)]
    c, roots = charpoly_roots(J)
    print(f"   a generic commutant element: characteristic polynomial coefficients {[str(x) for x in c]}; rational eigenvalues {[str(r) for r in roots]}")
    spaces = []
    for lam in roots:
        Ml = [[J[i][j] - (lam if i == j else 0) for j in range(4)] for i in range(4)]
        ker = nullspace([Ml[i][:] for i in range(4)], 4)
        spaces.append((lam, ker)); print(f"   eigenvalue {lam}: invariant subspace of dimension {len(ker)}, basis {[[str(x) for x in v] for v in ker]}")
    if sum(len(k) for _, k in spaces) == 4:
        bases[n] = [v for _, k in spaces for v in k]
    else:
        print("   (eigenvalues not all rational: the splitting needs an extension field; stopping the exact part for this mode)")
if len(bases) == 3:
    # change of basis: new coordinates = coefficients on the basis vectors; A_n has the basis vectors as COLUMNS, so x = A_n x'
    A = {n: [[bases[n][j][i] for j in range(4)] for i in range(4)] for n in "XYZ"}   # columns = basis vectors
    Ai = {n: inv(A[n]) for n in "XYZ"}
    # the tensor in the new coordinates: U' = Ai_X U A_Y (bilinear form coefficients transform contragrediently); check by the trace identity
    U2 = [mm(mm(Ai["X"], U[k]), A["Y"]) for k in range(48)]
    V2 = [mm(mm(Ai["Y"], V[k]), A["Z"]) for k in range(48)]
    W2 = [mm(mm(Ai["Z"], W[k]), A["X"]) for k in range(48)]
    if not cyclic_ok(U2, V2, W2):
        U2 = [mm(mm(A["X"], U[k]), Ai["Y"]) for k in range(48)]; V2 = [mm(mm(A["Y"], V[k]), Ai["Z"]) for k in range(48)]; W2 = [mm(mm(A["Z"], W[k]), Ai["X"]) for k in range(48)]
        assert cyclic_ok(U2, V2, W2), "transformed scheme fails the trace identity"
    d = {n: [len(k) for _, k in [(None, bases[n][:2]), (None, bases[n][2:])]] for n in "XYZ"}
    def blocks(M, rsplit, csplit):
        pat = []
        for (r0, r1) in rsplit:
            for (c0, c1) in csplit:
                pat.append(int(any(M[i][j] != 0 for i in range(r0, r1) for j in range(c0, c1))))
        return tuple(pat)
    def kron2(M):
        "is the 4x4 matrix a Kronecker product of two 2x2 matrices (block matrix of rank 1 as a 2x2 array of 2x2 blocks)?"
        B = [[M[2*a+i][2*b+j] for i in range(2) for j in range(2)] for a in range(2) for b in range(2)]  # 4 blocks x 4 entries
        # rank of the 4x4 matrix whose rows are the flattened blocks
        return len(nullspace([r[:] for r in B], 4)) >= 3
    sp = [(0, 2), (2, 4)]
    pats = Counter(); kr = Counter()
    for k in range(48):
        pats[(blocks(U2[k], sp, sp), blocks(V2[k], sp, sp), blocks(W2[k], sp, sp))] += 1
        kr[(kron2(U2[k]), kron2(V2[k]), kron2(W2[k]))] += 1
    print("\nin the adapted bases (first two coordinates = first invariant plane), nonzero 2x2 blocks per factor (U, V, W), counted over the 48 terms:")
    for p, c in sorted(pats.items(), key=lambda t: -t[1]): print(f"   {c:2d} x  U{p[0]} V{p[1]} W{p[2]}")
    print(f"terms whose factors are Kronecker products of 2x2 matrices (U, V, W): {dict(kr)}")
    rk = Counter((sum(1 for _ in []),) for _ in [])
    json.dump({"A": {n: [[str(x) for x in r] for r in A[n]] for n in "XYZ"}}, open(sys.argv[3] if len(sys.argv) > 3 else "/dev/null", "w"))
