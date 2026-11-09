"""Rank structure over Q of a <4x4x4:r> scheme given as PLinOpt sms triplet PREFIX_{L,R,P}.sms
(L, R: r x 16 rows = the 4x4 factors row-major; P: 16 x r, column m = the 4x4 output factor):
per-term rank triples, the number of [1,1,1] terms, per-slot rank histograms, and for the rank-1
factors the distinct vectors (up to scale) in each position and the unions that test the
'3 x 12 vectors u, x, y' picture (a = u x^T, b = x y^T, c = y u^T up to the C convention).
usage: q48_structure.py PREFIX..."""
import sys
from fractions import Fraction
from collections import Counter
def read_sms(path):
    with open(path) as f:
        hdr = f.readline()
        while hdr.startswith('#') or not hdr.strip():
            hdr = f.readline()
        rows, cols, _ = hdr.split()
        rows, cols = int(rows), int(cols)
        M = [[Fraction(0)] * cols for _ in range(rows)]
        for ln in f:
            p = ln.split()
            if len(p) < 3: continue
            i, j, v = int(p[0]), int(p[1]), p[2]
            if i == 0 and j == 0: break
            M[i-1][j-1] = Fraction(v)
    return M
def rank(M):
    M = [row[:] for row in M]; r = 0; rows = len(M); cols = len(M[0])
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r
def norm(v):
    v = list(v)
    for x in v:
        if x != 0:
            return tuple(y / x for y in v)
    return None
def rank1_vectors(A):   # A = v w^T: return (v, w) normalized up to scale
    i = next(i for i in range(4) if any(A[i][j] != 0 for j in range(4)))
    w = norm(A[i]); j = next(j for j in range(4) if A[i][j] != 0)
    v = norm([A[k][j] for k in range(4)])
    return v, w
for pre in sys.argv[1:]:
    Lm, Rm, Pm = read_sms(pre + "_L.sms"), read_sms(pre + "_R.sms"), read_sms(pre + "_P.sms")
    r = len(Lm); assert len(Rm) == r and len(Pm[0]) == r
    mats = []
    for m in range(r):
        a = [Lm[m][4*i:4*i+4] for i in range(4)]
        b = [Rm[m][4*i:4*i+4] for i in range(4)]
        c = [[Pm[4*i+j][m] for j in range(4)] for i in range(4)]
        mats.append((a, b, c))
    trip = [(rank(a), rank(b), rank(c)) for a, b, c in mats]
    types = Counter(tuple(sorted(t)) for t in trip)
    n111 = sum(1 for t in trip if t == (1, 1, 1))
    hist = [Counter(t[k] for t in trip) for k in range(3)]
    pos = [set() for _ in range(6)]   # a-left, a-right, b-left, b-right, c-left, c-right
    for (a, b, c), t in zip(mats, trip):
        if t == (1, 1, 1):
            for k, M in enumerate((a, b, c)):
                v, w = rank1_vectors(M); pos[2*k].add(v); pos[2*k+1].add(w)
    aL, aR, bL, bR, cL, cR = pos
    print(f"{pre.split('/')[-1]}: rank {r}; [1,1,1] terms {n111}; sorted-type multiset {dict(sorted(types.items()))}")
    print(f"   per-slot rank histograms a {dict(sorted(hist[0].items()))} b {dict(sorted(hist[1].items()))} c {dict(sorted(hist[2].items()))}")
    print(f"   distinct vectors among the [1,1,1] factors: a-left {len(aL)} a-right {len(aR)} b-left {len(bL)} b-right {len(bR)} c-left {len(cL)} c-right {len(cR)}")
    print(f"   cyclic unions (c as c_ij): a-right|b-left {len(aR|bL)}, b-right|c-left {len(bR|cL)}, c-right|a-left {len(cR|aL)};  (c as c_ji): b-right|c-right {len(bR|cR)}, c-left|a-left {len(cL|aL)}")
