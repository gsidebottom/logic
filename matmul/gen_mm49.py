#!/usr/bin/env python3
"""Emit matmul/mm49: Strassen (x) Strassen — the 4x4 rank-49 integer
scheme, as an L/R/P SMS trio in the engine's convention (L,R:
49 x 16 rows = summands over row-major vec(A), vec(B); P: 16 x 49,
rows = output cells z = 4*i + j, cols = summands).  This is the
canonical F_2 flip-graph starting point (Kauers-Moosbauer walked
49 -> 47 mod 2 from here); entries are {-1,0,1} so the same trio
loads over ANY prime (goldilocks verify = the sign-safe gate).
"""
import os

# Strassen 2x2: (alpha, beta, gamma) per product, as 2x2 int matrices
S = [
    # M1 = (a11+a22)(b11+b22); C11 += M1, C22 += M1
    ([[1, 0], [0, 1]], [[1, 0], [0, 1]], [[1, 0], [0, 1]]),
    # M2 = (a21+a22) b11;      C21 += M2, C22 -= M2
    ([[0, 0], [1, 1]], [[1, 0], [0, 0]], [[0, 0], [1, -1]]),
    # M3 = a11 (b12-b22);      C12 += M3, C22 += M3
    ([[1, 0], [0, 0]], [[0, 1], [0, -1]], [[0, 1], [0, 1]]),
    # M4 = a22 (b21-b11);      C11 += M4, C21 += M4
    ([[0, 0], [0, 1]], [[-1, 0], [1, 0]], [[1, 0], [1, 0]]),
    # M5 = (a11+a12) b22;      C11 -= M5, C12 += M5
    ([[1, 1], [0, 0]], [[0, 0], [0, 1]], [[-1, 1], [0, 0]]),
    # M6 = (a21-a11)(b11+b12); C22 += M6
    ([[-1, 0], [1, 0]], [[1, 1], [0, 0]], [[0, 0], [0, 1]]),
    # M7 = (a12-a22)(b21+b22); C11 += M7
    ([[0, 1], [0, -1]], [[0, 0], [1, 1]], [[1, 0], [0, 0]]),
]

def kron(m, n):
    """2x2 (x) 2x2 -> 4x4, block structure out[2I+i][2J+j]."""
    out = [[0] * 4 for _ in range(4)]
    for I in range(2):
        for J in range(2):
            for i in range(2):
                for j in range(2):
                    out[2 * I + i][2 * J + j] = m[I][J] * n[i][j]
    return out

summands = []
for (a1, b1, c1) in S:
    for (a2, b2, c2) in S:
        summands.append((kron(a1, a2), kron(b1, b2), kron(c1, c2)))
assert len(summands) == 49

os.makedirs("mm49", exist_ok=True)

def vec(m):  # row-major 16-vector
    return [m[i][j] for i in range(4) for j in range(4)]

def write_sms(path, rows, ncols):
    with open(path, "w") as f:
        f.write(f"{len(rows)} {ncols} M\n")
        for ri, row in enumerate(rows):
            for ci, v in enumerate(row):
                if v:
                    f.write(f"{ri + 1} {ci + 1} {v}\n")
        f.write("0 0 0\n")

write_sms("mm49/L.sms", [vec(a) for a, _, _ in summands], 16)
write_sms("mm49/R.sms", [vec(b) for _, b, _ in summands], 16)
# P: 16 x 49 (row = output cell z, col = summand)
pt = [[0] * 49 for _ in range(16)]
for si, (_, _, c) in enumerate(summands):
    for z, v in enumerate(vec(c)):
        pt[z][si] = v
write_sms("mm49/P.sms", pt, 49)
print("mm49 written: 49 summands, entries in {-1,0,1}")
