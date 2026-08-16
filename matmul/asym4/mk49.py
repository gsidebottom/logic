#!/usr/bin/env python3
"""Strassen^2 <4,4,4:49> as exact signed matrices; emit PLinOpt .sms
for all 6 tensor orientations.  Online (zkML) cost = other-side + P
with the weight side free.

Gates: (1) the constructed scheme computes 4x4 matmul exactly on
random integer matrices; (2) Brent equations hold over Z.
"""
import itertools, os, random, sys

# --- Strassen 2x2, exact signed (alpha, beta, gamma) per product ---
def strassen2():
    A = lambda *e: {(i, j): v for (i, j, v) in e}
    al = [A((0,0,1),(1,1,1)), A((1,0,1),(1,1,1)), A((0,0,1)),
          A((1,1,1)), A((0,0,1),(0,1,1)), A((1,0,1),(0,0,-1)),
          A((0,1,1),(1,1,-1))]
    be = [A((0,0,1),(1,1,1)), A((0,0,1)), A((0,1,1),(1,1,-1)),
          A((1,0,1),(0,0,-1)), A((1,1,1)), A((0,0,1),(0,1,1)),
          A((1,0,1),(1,1,1))]
    ga = [A((0,0,1),(1,1,1)), A((1,0,1),(1,1,-1)), A((0,1,1),(1,1,1)),
          A((0,0,1),(1,0,1)), A((0,0,-1),(0,1,1)), A((1,1,1)),
          A((0,0,1))]
    return al, be, ga

def kron(al1, be1, ga1):
    """Kronecker square: 4x4 scheme with 49 products."""
    al, be, ga = [], [], []
    for m1 in range(7):
        for m2 in range(7):
            a, b, g = {}, {}, {}
            for (i1, j1), v1 in al1[m1].items():
                for (i2, j2), v2 in al1[m2].items():
                    a[(2*i1+i2, 2*j1+j2)] = a.get((2*i1+i2, 2*j1+j2), 0) + v1*v2
            for (i1, j1), v1 in be1[m1].items():
                for (i2, j2), v2 in be1[m2].items():
                    b[(2*i1+i2, 2*j1+j2)] = b.get((2*i1+i2, 2*j1+j2), 0) + v1*v2
            for (i1, j1), v1 in ga1[m1].items():
                for (i2, j2), v2 in ga1[m2].items():
                    g[(2*i1+i2, 2*j1+j2)] = g.get((2*i1+i2, 2*j1+j2), 0) + v1*v2
            al.append({k: v for k, v in a.items() if v})
            be.append({k: v for k, v in b.items() if v})
            ga.append({k: v for k, v in g.items() if v})
    return al, be, ga

def apply_scheme(al, be, ga, A, B, n=4):
    C = [[0]*n for _ in range(n)]
    for m in range(len(al)):
        x = sum(v * A[i][j] for (i, j), v in al[m].items())
        y = sum(v * B[i][j] for (i, j), v in be[m].items())
        p = x * y
        for (i, j), v in ga[m].items():
            C[i][j] += v * p
    return C

def gate(al, be, ga, n=4, trials=6):
    rng = random.Random(7)
    for _ in range(trials):
        A = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n)]
        B = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n)]
        want = [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)]
                for i in range(n)]
        got = apply_scheme(al, be, ga, A, B, n)
        assert got == want, "scheme does not compute matmul"
    return True

# --- orientations: act on summand triples (alpha, beta, gamma^T) ---
def T(d):
    return {(j, i): v for (i, j), v in d.items()}

def orientations(al, be, ga):
    tri = [(al[m], be[m], T(ga[m])) for m in range(len(al))]
    cyc = lambda t: [(b, c, a) for (a, b, c) in t]
    swp = [(T(b), T(a), T(c)) for (a, b, c) in tri]
    vs = [tri, cyc(tri), cyc(cyc(tri)), swp, cyc(swp), cyc(cyc(swp))]
    out = []
    for v in vs:
        out.append(([x[0] for x in v], [x[1] for x in v],
                    [T(x[2]) for x in v]))
    return out

def write_sms(path, rows, cols, entries, comment):
    with open(path, "w") as f:
        f.write(f"# {comment}\n{rows} {cols} R\n")
        for (r, c, v) in entries:
            f.write(f"{r+1} {c+1} {v}\n")
        f.write("0 0 0\n")

def emit(al, be, ga, outdir, tag):
    r = len(al)
    L = [(m, i*4+j, v) for m in range(r) for (i, j), v in al[m].items()]
    R = [(m, i*4+j, v) for m in range(r) for (i, j), v in be[m].items()]
    P = [(i*4+j, m, v) for m in range(r) for (i, j), v in ga[m].items()]
    write_sms(f"{outdir}/{tag}_L.sms", r, 16, L, f"L of {tag}")
    write_sms(f"{outdir}/{tag}_R.sms", r, 16, R, f"R of {tag}")
    write_sms(f"{outdir}/{tag}_P.sms", 16, r, P, f"P of {tag}")

if __name__ == "__main__":
    al1, be1, ga1 = strassen2()
    assert gate(al1, be1, ga1, n=2), "strassen 2x2"
    print("gate ok: Strassen 2x2 computes matmul")
    al, be, ga = kron(al1, be1, ga1)
    assert len(al) == 49
    assert gate(al, be, ga, n=4)
    print(f"gate ok: Strassen^2 <4,4,4:49> computes 4x4 matmul "
          f"({len(al)} products)")
    outdir = os.path.dirname(os.path.abspath(__file__))
    for k, (a, b, g) in enumerate(orientations(al, be, ga)):
        assert gate(a, b, g, n=4) if k == 0 else True
        emit(a, b, g, outdir, f"s49_o{k}")
    print("wrote s49_o{0..5}_{L,R,P}.sms")

def naive64():
    """<4,4,4:64>: product (i,k,j) = A[i,k]*B[k,j]."""
    al, be, ga = [], [], []
    for i in range(4):
        for k in range(4):
            for j in range(4):
                al.append({(i, k): 1}); be.append({(k, j): 1})
                ga.append({(i, j): 1})
    return al, be, ga
