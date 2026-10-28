#!/usr/bin/env python3
"""Write a square scheme (role 0, our convention) as PLinOpt .slp direct-sum programs and .sms
matrices: PREFIX_{L,R,P}.slp and .sms.   python3 -I mk_slp.py SPEC PREFIX   (SPEC as in orbit5.py)"""
import os, sys
if sys.flags.isolated:
    sys.path.append("/Users/greg/Library/Python/3.9/lib/python/site-packages")
    sys.path.append(os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import screen5, orbit5

def slp(M, var_in="i", var_out="o"):
    lines = []
    for k, row in enumerate(M):
        terms = []
        for j in np.nonzero(row)[0]:
            c = row[j]
            if c == 1: terms.append(f"+{var_in}{j}")
            elif c == -1: terms.append(f"-{var_in}{j}")
            else: terms.append(f"{c:+g}*{var_in}{j}")
        s = "".join(terms)
        lines.append(f"{var_out}{k}:={s[1:] if s.startswith('+') else s};")
    return "\n".join(lines) + "\n"

def sms(M):
    r, c = M.shape
    out = [f"{r} {c} M"]
    for i in range(r):
        for j in range(c):
            if M[i, j] != 0:
                out.append(f"{i+1} {j+1} {M[i, j]:g}")
    out.append("0 0 0")
    return "\n".join(out) + "\n"

name, n, a, b, c = orbit5.load(sys.argv[1])
L, R, P = screen5.to_LRP(a, b, c, n, np.random.default_rng(1))
prefix = sys.argv[2]
for side, M in (("L", L), ("R", R), ("P", P)):
    open(f"{prefix}_{side}.slp", "w").write(slp(M))
    open(f"{prefix}_{side}.sms", "w").write(sms(M))
print(f"{name}: L {L.shape} R {R.shape} P {P.shape} -> {prefix}_{{L,R,P}}.{{slp,sms}}; operations {int((L!=0).sum()+(R!=0).sum()+(P!=0).sum()) - L.shape[0]*2 - P.shape[0]} additions")
