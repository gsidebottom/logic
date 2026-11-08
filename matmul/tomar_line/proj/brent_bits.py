"""Independent Brent check of <4,4,4> .bits schemes over F2 (pure Python).
Layout: the r alpha matrices, then the r betas, then the r gammas (each 4x4 row-major), one line of 0/1.
Tries both gamma conventions (gamma_s[i,j] multiplies c_ij, or c_ji) and
reports which one every scheme satisfies.  usage: brent_bits.py FILE..."""
import sys
N = 4
def load(path):
    b = open(path).read().split()[-1]
    w = 3 * N * N
    r = len(b) // w
    assert r * w == len(b), path
    A, B, C = [], [], []
    q = N * N
    for s in range(r):           # blocks: all alphas, then all betas, then all gammas
        a = b[s*q:(s+1)*q]; be = b[r*q + s*q: r*q + (s+1)*q]; g = b[2*r*q + s*q: 2*r*q + (s+1)*q]
        A.append([[int(a[i*N+k]) for k in range(N)] for i in range(N)])
        B.append([[int(be[k*N+j]) for j in range(N)] for k in range(N)])
        C.append([[int(g[i*N+j]) for j in range(N)] for i in range(N)])
    return r, A, B, C
def violations(r, A, B, C, transposed):
    bad = 0
    for i in range(N):
        for k in range(N):
            for k2 in range(N):
                for j in range(N):
                    for i2 in range(N):
                        for j2 in range(N):
                            acc = 0
                            for s in range(r):
                                if A[s][i][k] and B[s][k2][j]:
                                    g = C[s][j2][i2] if transposed else C[s][i2][j2]
                                    acc ^= g
                            want = 1 if (k == k2 and i == i2 and j == j2) else 0
                            if acc != want:
                                bad += 1
    return bad
for p in sys.argv[1:]:
    r, A, B, C = load(p)
    v0 = violations(r, A, B, C, False)
    v1 = violations(r, A, B, C, True)
    print(f"{p.split('/')[-1]}: rank {r}, violations gamma=(i,j) {v0}, gamma=(j,i) {v1}")
