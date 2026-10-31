#!/usr/bin/env python3
"""One exact point per P pattern with at least 8 canonical columns (canon_classes.py): A from the selected
row lines and C^-1 from the selected column lines of the base point, B the base's.  Diagonal scalings by
powers of two are chosen to minimize the non-unit coefficients of P (per-column scale free).  Writes the
points, checks all Brent equations exactly, and reports what the P side looks like.

  pclasses.py PREFIX CANON_P.json OUTDIR
"""
import itertools, json, os, sys
src = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/canon_enum.py').read()
pre, cj, outd = sys.argv[1:4]
sys.argv = ['x', pre, '/dev/null']
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()): exec(src[:src.index('t = time.time()')])
os.makedirs(outd, exist_ok=True)
def inv(M):
    A = [[Fr(x) for x in r] + [Fr(i == j) for j in range(4)] for i, r in enumerate(M)]
    for c in range(4):
        p = next(r for r in range(c, 4) if A[r][c]); A[c], A[p] = A[p], A[c]
        d = A[c][c]; A[c] = [x / d for x in A[c]]
        for r in range(4):
            if r != c and A[r][c]:
                f = A[r][c]; A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [r[4:] for r in A]
def mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
I4 = [[Fr(i == j) for j in range(4)] for i in range(4)]
Wn = [[[Fr(x) for x in r] for r in w] for w in W]; Un = [[[Fr(x) for x in r] for r in u] for u in U]; Vn = [[[Fr(x) for x in r] for r in v] for v in V]
def fmt(x): return str(Fr(x))
def write(prefix, Us, Vs, Ws):
    with open(prefix + "_L.sms", "w") as f:
        f.write("48 16 R\n")
        for k in range(48):
            for i, j in itertools.product(range(4), repeat=2):
                if Us[k][i][j]: f.write(f"{k + 1} {i * 4 + j + 1} {fmt(Us[k][i][j])}\n")
        f.write("0 0 0\n")
    with open(prefix + "_R.sms", "w") as f:
        f.write("48 16 R\n")
        for k in range(48):
            for i, j in itertools.product(range(4), repeat=2):
                if Vs[k][i][j]: f.write(f"{k + 1} {i * 4 + j + 1} {fmt(Vs[k][i][j])}\n")
        f.write("0 0 0\n")
    with open(prefix + "_P.sms", "w") as f:
        f.write("16 48 R\n")
        for i, j in itertools.product(range(4), repeat=2):        # row i*4+j of P: coefficient of C[i][j]; W is the transposed column
            for k in range(48):
                if Ws[k][j][i]: f.write(f"{i * 4 + j + 1} {k + 1} {fmt(Ws[k][j][i])}\n")
        f.write("0 0 0\n")
def brent(Us, Vs, Ws):
    den = 1
    for T_ in (Us, Vs, Ws):
        for m in T_:
            for r in m:
                for x in r: den = den * x.denominator // gcd(den, x.denominator)
    u, v, w = (np.array([[[int(x * den) for x in r] for r in m] for m in T_], dtype=object) for T_ in (Us, Vs, Ws))
    Tn = np.einsum('kab,kcd,kef->abcdef', u, v, w, optimize=False)
    for a, b, c, d, e, f in itertools.product(range(4), repeat=6):
        want = den ** 3 if (b == c and d == e and f == a) else 0
        if Tn[a, b, c, d, e, f] != want: return False
    return True
rows_out = []
for ci, (cP, nnzp, pairs) in enumerate(sorted(json.load(open(cj)), key=lambda r: (-r[0], r[1]))):
    z, x = pairs[0]
    sz, qx = sel["Z"][z][0], sel["X"][x][1]
    S = [col["Z"][i] for i in range(8) if (sz >> i) & 1]; Q = [row["X"][i] for i in range(8) if (qx >> i) & 1]
    Ci = [[Fr(S[j][i]) for j in range(4)] for i in range(4)]; A = [[Fr(v) for v in r] for r in Q]
    C_ = inv(Ci); Ai = inv(A)
    Wp = np.array([[[float(y) for y in r] for r in mm(mm(C_, w), Ai)] for w in Wn])
    nz = [np.abs(w) > 1e-9 for w in Wp]
    # non-unit count under diagonal powers of two
    pw = np.array(list(itertools.product((-1, 0, 1), repeat=4)))
    best = None
    lg = [np.where(np.abs(w) > 1e-9, np.log2(np.abs(w) + 1e-30), 0.0) for w in Wp]
    for dc in pw:
        for da in pw:
            nu = 0
            for w, l, m in zip(Wp, lg, nz):
                e = (l + dc[:, None] - da[None, :])[m]
                v, c = np.unique(np.round(e, 6), return_counts=True); nu += e.size - c.max()
            if best is None or nu < best[0]: best = (nu, dc.copy(), da.copy())
    nu, dc, da = best
    Dc = [[Fr(2) ** int(dc[i]) if i == j else Fr(0) for j in range(4)] for i in range(4)]; Da = [[Fr(2) ** int(da[i]) if i == j else Fr(0) for j in range(4)] for i in range(4)]
    A2 = mm(Da, A); A2i = inv(A2); C2 = mm(Dc, C_); C2i = inv(C2)
    Us = [mm(A2, u) for u in Un]; Vs = [mm(v, C2i) for v in Vn]; Ws = [mm(mm(C2, w), A2i) for w in Wn]
    for k in range(48):     # put each P column on magnitude 1 where most entries sit, compensating in L
        vals = Counter(abs(y) for r in Ws[k] for y in r if y); m_ = vals.most_common(1)[0][0]
        Ws[k] = [[y / m_ for y in r] for r in Ws[k]]; Us[k] = [[y * m_ for y in r] for r in Us[k]]
    dy = all(Fr(y).denominator & (Fr(y).denominator - 1) == 0 for r_ in (Ws,) for m in r_ for rr in m for y in rr)
    tag = f"c{cP}_n{nnzp}_{ci}"
    write(f"{outd}/{tag}", Us, Vs, Ws)
    ok = brent(Us, Vs, Ws)
    can = sum(1 for k in range(48) if sum(1 for r in Ws[k] for y in r if y) == 1)
    nun = sum(1 for k in range(48) for r in Ws[k] for y in r if y and abs(y) != 1)
    print(f"{tag:14s} Brent {int(ok)}  dyadic P {int(dy)}  canon {can}  non-unit in P {nun}", flush=True)
    rows_out.append(dict(tag=tag, cP=cP, nnz=nnzp, brent=int(ok), dyadic=int(dy), nonunit=nun))
json.dump(rows_out, open(f"{outd}/classes.json", "w"))
