"""Convert a Mathematica-list scheme (.m: a list of products, each {A, B, C} with A n1 x n2, B n2 x n3 and C either
n1 x n3 or its transpose n3 x n1, integer or rational entries (an odd denominator is a unit mod 2); the layout of Moosbauer's flip-graph repository and of the
Perminov catalog's meta_flip_graph entries) to the repository's .bits layout over F2 (alpha (r,n1,n2), beta
(r,n2,n3), gamma (r,n1,n3), row-major, one line), verifying the Brent equations first.  Entries are reduced mod 2;
a product with a factor that vanishes mod 2 is dropped (reported), so an integer scheme's F2 image can have a
smaller rank.  Both C readings are tried when the format is square.
usage: m_to_bits.py in.m N1 N2 N3 out.bits"""
import sys, json, re
src, n1, n2, n3, dst = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
text = ''.join(open(src).read().split()).replace('{', '[').replace('}', ']')
def frac(m):  # p/q with q odd is p mod 2 (q is a unit); an even q has no image mod 2
    assert int(m.group(2)) % 2, 'even denominator ' + m.group(0) + ': the scheme has no reduction mod 2'
    return m.group(1)
text = re.sub(r'(-?\d+)/(\d+)', frac, text)
prods = json.loads(text)
terms = []; dropped = 0
for p in prods:
    assert len(p) == 3, 'a product is not a triple'
    A, B, C = p
    assert len(A) == n1 and all(len(row) == n2 for row in A), 'A shape'
    assert len(B) == n2 and all(len(row) == n3 for row in B), 'B shape'
    c_t = len(C) == n3 and all(len(row) == n1 for row in C)
    assert c_t or (len(C) == n1 and all(len(row) == n3 for row in C)), 'C shape'
    red = lambda X: [[int(x) % 2 for x in row] for row in X]
    A, B, C = red(A), red(B), red(C)
    if not any(map(any, A)) or not any(map(any, B)) or not any(map(any, C)): dropped += 1; continue
    terms.append((A, B, C, c_t))
r = len(terms)
print(f"{len(prods)} products read, {dropped} vanish mod 2, rank over F2 {r}")
def build(transpose_c):
    al = [t[0] for t in terms]; be = [t[1] for t in terms]; ga = []
    for A, B, C, c_t in terms:
        if transpose_c:
            if not (len(C) == n3 and len(C[0]) == n1): return None
            ga.append([[C[j][i] for j in range(n3)] for i in range(n1)])
        else:
            if not (len(C) == n1 and len(C[0]) == n3): return None
            ga.append(C)
    return al, be, ga
def brent(al, be, ga):
    bad = 0
    for i in range(n1):
        for k in range(n2):
            T = [t for t in range(r) if al[t][i][k]]
            for k2 in range(n2):
                for j in range(n3):
                    T2 = [t for t in T if be[t][k2][j]]
                    for i2 in range(n1):
                        for j2 in range(n3):
                            s = sum(ga[t][i2][j2] for t in T2) & 1
                            if s != int(k == k2 and i == i2 and j == j2): bad += 1
    return bad
chosen = None
for ct in (True, False):
    b = build(ct)
    if b is None: print(f"c transposed={ct}: shape mismatch, impossible"); continue
    bad = brent(*b); print(f"c transposed={ct}: {bad} of {n1*n2*n2*n3*n1*n3} Brent equations violated")
    if bad == 0: chosen = (ct, b)
assert chosen is not None, 'neither reading satisfies the Brent equations'
ct, (al, be, ga) = chosen
bits = ''.join(str(x) for t in range(r) for row in al[t] for x in row) + ''.join(str(x) for t in range(r) for row in be[t] for x in row) + ''.join(str(x) for t in range(r) for row in ga[t] for x in row)
open(dst, 'w').write(bits + '\n')
print(f"wrote {dst}: rank {r}, {len(bits)} bits, c read as c_(j,i)={ct}")
