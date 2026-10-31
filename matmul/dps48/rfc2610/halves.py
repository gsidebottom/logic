import sys
from fractions import Fraction
def read_sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = [[Fraction(0)] * c for _ in range(r)]
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1][int(t[1]) - 1] = Fraction(t[2])
    return M
d = sys.argv[1]
L, R, P = (read_sms(f"{d}/4x4x4_48_203_{m}.sms") for m in "LRP")
hl = [i for i, row in enumerate(L) if any(abs(x) == Fraction(1, 2) for x in row)]
hr = [i for i, row in enumerate(R) if any(abs(x) == Fraction(1, 2) for x in row)]
p2 = [i for i in range(48) if any(abs(P[j][i]) == 2 for j in range(16))]
print("products whose L row has a 1/2:", hl)
print("products whose R row has a 1/2:", hr)
print("products whose P column has a 2: ", p2)
for i in sorted(set(hl) | set(hr) | set(p2)):
    lv = sorted(set(abs(x) for x in L[i] if x)); rv = sorted(set(abs(x) for x in R[i] if x)); pv = sorted(set(abs(P[j][i]) for j in range(16) if P[j][i]))
    print(f"  product {i}: |L| {[str(x) for x in lv]}, |R| {[str(x) for x in rv]}, |P| {[str(x) for x in pv]}")
