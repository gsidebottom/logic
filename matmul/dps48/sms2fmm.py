#!/usr/bin/env python3
"""Convert a PLinOpt scheme (PREFIX_{L,R,P}.sms over Z[1/2]) to the text format
of Martensson's fmm_add_reduction: three integer blocks separated by '#',
rows = the 16 entries of A, B, C (row-major), columns = the products.

Rank-48 schemes need 1/2, so no integer representative exists; L and R are
scaled by the smallest power of two that clears their denominators (the
scheme then computes a multiple of C, which only the tool's correctness
check notices -- use the patched build that warns instead of aborting).
The addition counts of the scaled L and R are those of L and R (scaling a
row does not change its additions), so the tool's A/B/C counts are
comparable to PLinOpt's addition counts (scalings excluded).

Usage: sms2fmm.py PREFIX OUT.txt
"""
import sys
from fractions import Fraction as Fr


def sms(path):
    M = None
    for ln in open(path):
        p = ln.split()
        if M is None:
            if len(p) >= 2 and p[0].isdigit() and p[1].isdigit():
                M = [[Fr(0)] * int(p[1]) for _ in range(int(p[0]))]
            continue
        if len(p) < 3 or (p[0] == "0" and p[1] == "0"):
            break
        M[int(p[0]) - 1][int(p[1]) - 1] = Fr(p[2])
    return M


def scale_factor(M):
    d = 1
    for row in M:
        for v in row:
            while (v * d).denominator != 1:
                d *= 2
    return d


def main():
    pre, out = sys.argv[1], sys.argv[2]
    L, R, P = sms(pre + "_L.sms"), sms(pre + "_R.sms"), sms(pre + "_P.sms")
    r = len(L)
    sL, sR, sP = scale_factor(L), scale_factor(R), scale_factor(P)
    blocks = []
    blocks.append([[int(L[k][e] * sL) for k in range(r)] for e in range(16)])
    blocks.append([[int(R[k][e] * sR) for k in range(r)] for e in range(16)])
    blocks.append([[int(P[e][k] * sP) for k in range(r)] for e in range(16)])
    with open(out, "w") as f:
        for i, b in enumerate(blocks):
            for row in b:
                f.write(" ".join(map(str, row)) + "\n")
            if i < 2:
                f.write("#\n")
    print(f"wrote {out}: scales L x{sL}, R x{sR}, P x{sP}")


if __name__ == "__main__":
    main()
