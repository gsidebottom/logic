# Are the 203 point's L and R rows the 204 point's up to a scalar per product?  If so the scalars are
# exactly the affine choice Alexandre's footnote describes, and the rescaling worth testing.
import sys
from fractions import Fraction as Fr
from collections import Counter
def read_sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = [[Fr(0)] * c for _ in range(r)]
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1][int(t[1]) - 1] = Fr(t[2])
    return M
def norm(v):
    f = next(x for x in v if x != 0); return tuple(x / f for x in v), f
d203, d204 = sys.argv[1], sys.argv[2]
L3, R3, P3 = (read_sms(f"{d203}/4x4x4_48_203_{m}.sms") for m in "LRP")
L4, R4, P4 = (read_sms(f"{d204}/4x4x4_48_204_{m}.sms") for m in "LRP")
for name, A, B in (("L", L3, L4), ("R", R3, R4), ("L203 vs R204", L3, R4), ("R203 vs L204", R3, L4)):
    idx = {}
    for j, row in enumerate(B): idx.setdefault(norm(row)[0], []).append((j, norm(row)[1]))
    hit = sum(1 for row in A if norm(row)[0] in idx)
    ratios = Counter(str(abs(norm(row)[1] / idx[norm(row)[0]][0][1])) for row in A if norm(row)[0] in idx)
    print(f"{name}: {hit}/48 rows match up to a scalar; |ratio 203/204| {dict(ratios)}")
