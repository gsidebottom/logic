"""Convert a Kauers-Moosbauer .exp scheme (lines "(a..+..)*(b..+..)*(c..+..)", mod 2) to the
repository's .bits layout (alpha (r,n1,n2), beta (r,n2,n3), gamma (r,n1,n3), row-major, one line),
verifying the Brent equations first.  The .exp writes the trilinear form sum a_ik b_kj c_ji, so c
is indexed (j,i); both readings are tried and the one that satisfies the equations is written.
usage: km_exp_to_bits.py in.exp N1 N2 N3 out.bits"""
import sys, re
src, n1, n2, n3, dst = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
lines = [l.strip() for l in open(src) if l.strip()]
var = re.compile(r'^([abc])(\d)(\d)$')
terms = []
for l in lines:
    assert '-' not in l, 'signed coefficient in a mod-2 file: ' + l
    parts = [p.strip() for p in l.split('*')]
    assert len(parts) == 3 and all(p[0] == '(' and p[-1] == ')' for p in parts), l
    groups = []
    for letter, p in zip('abc', parts):
        vs = []
        for v in p[1:-1].split('+'):
            m = var.match(v.strip()); assert m and m.group(1) == letter, (l, v)
            vs.append((int(m.group(2)), int(m.group(3))))
        groups.append(vs)
    terms.append(groups)
r = len(terms)
def build(c_transposed):
    al = [[[0]*n2 for _ in range(n1)] for _ in range(r)]
    be = [[[0]*n3 for _ in range(n2)] for _ in range(r)]
    ga = [[[0]*n3 for _ in range(n1)] for _ in range(r)]
    for t, (A, B, C) in enumerate(terms):
        for i, k in A: al[t][i-1][k-1] ^= 1
        for k, j in B: be[t][k-1][j-1] ^= 1
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
