"""For each mode: the involution K spanning the stabilizer's commutant with I (eigenspaces = the two invariant
planes), and whether the 32 trivial-slot elements act on the two planes by equivalent representations (compare
the characters of the restrictions).  usage: q3_reps.py STAB.json"""
import sys, json
from fractions import Fraction as Fr
from collections import Counter
el = json.load(open(sys.argv[1])); triv = [e for e in el if e['slot'] == 'id']
def tomat(m): return [[Fr(str(x)) for x in row] for row in m]
def mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
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
    free = [c for c in range(nvar) if c not in piv]; out = []
    for fc in free:
        v = [Fr(0)] * nvar; v[fc] = Fr(1)
        for i, pc in enumerate(piv): v[pc] = -A[i][fc]
        out.append(v)
    return out
def solve(A, b):  # least-squares-free exact solve of A x = b (A 4x2 or 4x4 full column rank) via normal equations avoided: use Gaussian on augmented
    n = len(A[0]); rows = [A[i][:] + [b[i]] for i in range(len(A))]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None: continue
        rows[r], rows[p] = rows[p], rows[r]; f = rows[r][c]; rows[r] = [x / f for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                g = rows[i][c]; rows[i] = [x - g * y for x, y in zip(rows[i], rows[r])]
        piv.append(c); r += 1
    x = [Fr(0)] * n
    for i, c in enumerate(piv): x[c] = rows[i][n]
    assert all(rows[i][n] == 0 for i in range(r, len(rows))), "inconsistent"
    return x
for n in "XYZ":
    G = []
    for e in triv:
        g = tomat(e[n]); s = next(x for row in g for x in row if x != 0); G.append([[x / abs(s) for x in row] for row in g])   # scale to primitive, sign kept
    eqs = []
    for g in G:
        for i in range(4):
            for j in range(4):
                row = [Fr(0)] * 16
                for k in range(4):
                    row[i * 4 + k] += -g[k][j]; row[k * 4 + j] += g[i][k]
                eqs.append(row)
    comm = nullspace(eqs, 16)
    # K = the commutant element with trace 0 normalised to K^2 = I (if the commutant is Q[K])
    B = [[[b[i * 4 + j] for j in range(4)] for i in range(4)] for b in comm]
    I = [[Fr(int(i == j)) for j in range(4)] for i in range(4)]
    K = None
    for b in B:
        t = sum(b[i][i] for i in range(4)); K0 = [[b[i][j] - (t / 4 if i == j else 0) for j in range(4)] for i in range(4)]
        if any(x != 0 for row in K0 for x in row):
            K2 = mm(K0, K0); lam = K2[0][0]
            assert all(K2[i][j] == (lam if i == j else 0) for i in range(4) for j in range(4)), "K^2 not scalar"
            K = K0; break
    print(f"mode {n}: commutant dimension {len(comm)}; traceless generator K with K^2 = {lam} * I:"); [print("    ", [str(x) for x in row]) for row in K]
    # eigenspaces of K
    planes = []
    for ev in sorted({Fr(1), Fr(-1)} if lam == 1 else set()):
        Ml = [[K[i][j] - (ev * 1 if i == j else 0) for j in range(4)] for i in range(4)]
        planes.append((ev, nullspace([r[:] for r in Ml], 4)))
    if lam != 1:
        print("    (K^2 is not I; eigenvalues +-sqrt of it: the planes are over an extension)"); continue
    # characters of the restrictions of the group to each plane: trace of g restricted = solve g*basis = basis*M
    chars = []
    for ev, basis in planes:
        Bm = [[basis[j][i] for j in range(len(basis))] for i in range(4)]   # 4 x 2, columns = basis vectors
        tr = []
        for g in G:
            gB = mm(g, Bm)   # 4 x 2
            M = [solve(Bm, [gB[i][c] for i in range(4)]) for c in range(2)]   # coordinates of g b_c in the basis
            tr.append(sum(M[c][c] for c in range(2)))
        chars.append((ev, tr))
        print(f"    plane K = {ev}: dimension {len(basis)}, character multiset {dict(sorted(Counter(str(t) for t in tr).items()))}")
    same = chars[0][1] == chars[1][1]
    print(f"    the two planes carry {'EQUIVALENT' if same else 'INEQUIVALENT'} representations of the 32-element group (characters {'equal' if same else 'differ'} elementwise)")
