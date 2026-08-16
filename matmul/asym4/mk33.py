#!/usr/bin/env python3
"""3x3 comparison: naive-27 vs a signed rank-23 scheme, emitted as
PLinOpt .sms over all 6 tensor orientations.  Gates both by exact
evaluation against 3x3 matmul on random integer matrices.
"""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mk49 import gate, orientations, write_sms

def naive27():
    al, be, ga = [], [], []
    for i in range(3):
        for k in range(3):
            for j in range(3):
                al.append({(i, k): 1}); be.append({(k, j): 1})
                ga.append({(i, j): 1})
    return al, be, ga

def from_coef(path, r=23, n=3):
    """621 signed coefficients (alpha block, beta, gamma) -> dicts."""
    c = [int(x) for x in open(path).read().split()]
    assert len(c) == 3 * r * n * n
    na = r * n * n
    al, be, ga = [], [], []
    for m in range(r):
        a, b, g = {}, {}, {}
        for i in range(n):
            for j in range(n):
                k = m * n * n + i * n + j
                if c[k]: a[(i, j)] = c[k]
                if c[na + k]: b[(i, j)] = c[na + k]
                if c[2 * na + k]: g[(i, j)] = c[2 * na + k]
        al.append(a); be.append(b); ga.append(g)
    return al, be, ga

def emit3(al, be, ga, outdir, tag, n=3):
    r = len(al)
    L = [(m, i*n+j, v) for m in range(r) for (i, j), v in al[m].items()]
    R = [(m, i*n+j, v) for m in range(r) for (i, j), v in be[m].items()]
    P = [(i*n+j, m, v) for m in range(r) for (i, j), v in ga[m].items()]
    write_sms(f"{outdir}/{tag}_L.sms", r, n*n, L, f"L {tag}")
    write_sms(f"{outdir}/{tag}_R.sms", r, n*n, R, f"R {tag}")
    write_sms(f"{outdir}/{tag}_P.sms", n*n, r, P, f"P {tag}")

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    nv = naive27()
    assert gate(*nv, n=3), "naive-27"
    print(f"gate ok: naive-27 computes 3x3 matmul ({len(nv[0])} products)")
    r23 = from_coef(f"{here}/best40.coef")
    assert gate(*r23, n=3), "rank-23 signed"
    print(f"gate ok: signed rank-23 computes 3x3 matmul ({len(r23[0])} products)")
    for k, (a, b, g) in enumerate(orientations(*nv)):
        emit3(a, b, g, here, f"n27_o{k}")
    for k, (a, b, g) in enumerate(orientations(*r23)):
        emit3(a, b, g, here, f"r23_o{k}")
    print("wrote n27/r23 orientations")
