"""Convert a Kauers-Moosbauer .exp scheme (one product per line, three factors joined by '*', each factor a
parenthesised sum or a bare monomial, integer coefficients allowed: "(a41-a42)*(b14+b15)*(-2*c11+c21)",
"a23*(...)*(...)") to the repository's .bits layout over F2 (alpha (r,n1,n2), beta (r,n2,n3), gamma (r,n1,n3),
row-major, one line), verifying the Brent equations first.  Coefficients are reduced mod 2; a product with a
factor that vanishes mod 2 is dropped (reported), so an integer scheme's F2 image can have a smaller rank.
The .exp writes the trilinear form sum a_ik b_kj c_ji, so c is indexed (j,i); both readings are tried and the one
that satisfies the equations is written.
usage: exp_to_bits.py in.exp N1 N2 N3 out.bits"""
import sys, re
src, n1, n2, n3, dst = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
lines = [l.strip().replace(' ', '') for l in open(src) if l.strip()]
BARE = r'[+-]?(?:\d+\*)?[abc]\d\d'
factor = r'(?:\(([^()]*)\)|(' + BARE + r'))'
line_re = re.compile('^' + factor + r'\*' + factor + r'\*' + factor + '$')
mono = re.compile(r'([+-]?)(?:(\d+)\*)?([abc])(\d)(\d)')
terms = []; dropped = 0
for l in lines:
    m = line_re.match(l); assert m, 'unparsed line: ' + l
    texts = [m.group(1) or m.group(2), m.group(3) or m.group(4), m.group(5) or m.group(6)]
    groups = []; zero = False
    for letter, text in zip('abc', texts):
        ent = {}
        consumed = 0
        for mm in mono.finditer(text):
            consumed += len(mm.group(0))
            assert mm.group(3) == letter, (l, text)
            k = int(mm.group(2)) if mm.group(2) else 1
            if k % 2: ent[(int(mm.group(4)), int(mm.group(5)))] = ent.get((int(mm.group(4)), int(mm.group(5))), 0) ^ 1
        assert consumed == len(text), ('unparsed characters in factor', text)
        vs = [ij for ij, v in ent.items() if v]
        if not vs: zero = True
        groups.append(vs)
    if zero: dropped += 1; continue
    terms.append(groups)
r = len(terms)
print(f"{len(lines)} products read, {dropped} vanish mod 2, rank over F2 {r}")
def build(c_transposed):
    al = [[[0]*n2 for _ in range(n1)] for _ in range(r)]
    be = [[[0]*n3 for _ in range(n2)] for _ in range(r)]
    ga = [[[0]*n3 for _ in range(n1)] for _ in range(r)]
    for t, (A, B, C) in enumerate(terms):
        for i, k in A:
            if not (1 <= i <= n1 and 1 <= k <= n2): return None
            al[t][i-1][k-1] ^= 1
        for k, j in B:
            if not (1 <= k <= n2 and 1 <= j <= n3): return None
            be[t][k-1][j-1] ^= 1
        for x, y in C:
            i, j = (y, x) if c_transposed else (x, y)
            if not (1 <= i <= n1 and 1 <= j <= n3): return None
            ga[t][i-1][j-1] ^= 1
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
    if b is None: print(f"c transposed={ct}: index out of range, impossible"); continue
    bad = brent(*b); print(f"c transposed={ct}: {bad} of {n1*n2*n2*n3*n1*n3} Brent equations violated")
    if bad == 0: chosen = (ct, b)
assert chosen is not None, 'neither reading satisfies the Brent equations'
ct, (al, be, ga) = chosen
bits = ''.join(str(x) for t in range(r) for row in al[t] for x in row) + ''.join(str(x) for t in range(r) for row in be[t] for x in row) + ''.join(str(x) for t in range(r) for row in ga[t] for x in row)
open(dst, 'w').write(bits + '\n')
print(f"wrote {dst}: rank {r}, {len(bits)} bits, c read as c_(j,i)={ct}")
