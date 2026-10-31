# Product rescalings of Alexandre's 203 point: L_i -> a L_i, R_i -> b R_i, P_*i -> P_*i / (ab), a free
# isotropy.  Writes every distinct matrix once and checks each of the six combinations exactly.
import sys
from fractions import Fraction as Fr
src, dst = sys.argv[1], sys.argv[2]
def read_sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = [[Fr(0)] * c for _ in range(r)]
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1][int(t[1]) - 1] = Fr(t[2])
    return M
def write_sms(path, M):
    with open(path, "w") as f:
        f.write(f"{len(M)} {len(M[0])} R\n")
        for i, row in enumerate(M):
            for j, x in enumerate(row):
                if x != 0: f.write(f"{i+1} {j+1} {x}\n")
        f.write("0 0 0\n")
def brent(L, R, P):
    bad = 0
    for a in range(4):
        for b in range(4):
            for c in range(4):
                for a2 in range(4):
                    for b2 in range(4):
                        for c2 in range(4):
                            s = sum(P[a*4+c2][i] * L[i][a2*4+b] * R[i][b2*4+c] for i in range(48))
                            bad += s != (1 if (a == a2 and b == b2 and c == c2) else 0)
    return bad
def scale_rows(M, S, k): return [[x * (k if i in S else 1) for x in row] for i, row in enumerate(M)]
def scale_cols(P, S, k): return [[x * (k if i in S else 1) for i, x in enumerate(row)] for row in P]
def transpose(P): return [[P[j][i] for j in range(16)] for i in range(48)]
def vals(M): return sorted({abs(x) for row in M for x in row if x != 0})
L, R, P = (read_sms(f"{src}/4x4x4_48_203_{m}.sms") for m in "LRP")
ALL = {i for i, row in enumerate(L) if any(abs(x) == Fr(1, 2) for x in row)}
P43 = {43}
assert len(ALL) == 16 and all(abs(x) in (0, Fr(1, 2)) for x in L[43]) and all(abs(x) in (0, Fr(1, 2)) for x in R[43])
mats = {"L_all2": scale_rows(L, ALL, 2), "R_all2": scale_rows(R, ALL, 2),
        "P_all_d2": scale_cols(P, ALL, Fr(1, 2)), "P_all_d4": scale_cols(P, ALL, Fr(1, 4)),
        "L_p43x2": scale_rows(L, P43, 2), "R_p43x2": scale_rows(R, P43, 2),
        "P_p43_d2": scale_cols(P, P43, Fr(1, 2)), "P_p43_d4": scale_cols(P, P43, Fr(1, 4)), "P_base": P}
for name, M in mats.items():
    if name != "P_base": write_sms(f"{dst}/{name}.sms", M)
    if name.startswith("P_"): write_sms(f"{dst}/Pt{name[1:]}.sms", transpose(M))
    print(f"{name:10s} coefficients {[str(x) for x in vals(M)]}")
combos = {"A": (mats["L_all2"], R, mats["P_all_d2"]), "B": (L, mats["R_all2"], mats["P_all_d2"]),
          "C": (mats["L_all2"], mats["R_all2"], mats["P_all_d4"]), "D": (mats["L_p43x2"], R, mats["P_p43_d2"]),
          "E": (L, mats["R_p43x2"], mats["P_p43_d2"]), "F": (mats["L_p43x2"], mats["R_p43x2"], mats["P_p43_d4"])}
for k, (a, b, c) in combos.items():
    print(f"variant {k}: Brent equations violated {brent(a, b, c)} of 4096")
