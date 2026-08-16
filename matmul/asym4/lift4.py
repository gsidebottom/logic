#!/usr/bin/env python3
"""Sign-lift a mod-2 4x4 rank-R bit tensor to an exact {-1,0,1} scheme.

Support is fixed by the bits; each nonzero coefficient is +-1.  For a
Brent equation with k covering terms and RHS r, the signed sum is
k - 2*(#negative terms) = r, so exactly (k-r)/2 terms must be
negative, and a term is negative iff the XOR of its three sign bits
is 1.  SAT over those sign bits; the model is verified by exact
evaluation against 4x4 matmul before it is accepted.

Usage: lift4.py FILE.bits [out.coef]
"""
import itertools, os, random, subprocess, sys

SAT = "./target/release/sat"

def load(path, R=49, n=4):
    b = [int(c) for c in open(path).read() if c in '01']
    assert len(b) == 3*R*n*n, f"{path}: {len(b)} bits"
    na = R*n*n
    g = lambda off, m, i, j: b[off + m*n*n + i*n + j]
    A = [[[g(0,m,i,j) for j in range(n)] for i in range(n)] for m in range(R)]
    B = [[[g(na,m,i,j) for j in range(n)] for i in range(n)] for m in range(R)]
    G = [[[g(2*na,m,i,j) for j in range(n)] for i in range(n)] for m in range(R)]
    return A, B, G

def build_cnf(A, B, G, R=49, n=4):
    var = {}
    def sv(kind, m, i, j):
        key = (kind, m, i, j)
        if key not in var: var[key] = len(var) + 1
        return var[key]
    for m in range(R):
        for i in range(n):
            for j in range(n):
                if A[m][i][j]: sv('a', m, i, j)
                if B[m][i][j]: sv('b', m, i, j)
                if G[m][i][j]: sv('g', m, i, j)
    nxt = [len(var) + 1]
    cls = []
    def xor3(x, y, z):
        """fresh t with t <-> x xor y xor z"""
        t = nxt[0]; nxt[0] += 1
        for sx in (0, 1):
            for sy in (0, 1):
                for sz in (0, 1):
                    par = sx ^ sy ^ sz
                    lit = lambda v, s: (-v if s else v)
                    # block the assignment (x=sx, y=sy, z=sz) unless t=par
                    cls.append([lit(x, sx), lit(y, sy), lit(z, sz),
                                (t if par else -t)])
        return t
    for a, bb, c, d, p, q in itertools.product(range(n), repeat=6):
        cov = [m for m in range(R)
               if A[m][a][bb] and B[m][c][d] and G[m][p][q]]
        if not cov: continue
        rhs = 1 if (bb == c and a == p and d == q) else 0
        k = len(cov)
        assert (k - rhs) % 2 == 0, "mod-2 invalid scheme"
        j = (k - rhs) // 2          # exactly j negative terms
        ts = [xor3(sv('a', m, a, bb), sv('b', m, c, d), sv('g', m, p, q))
              for m in cov]
        # binomial exactly-j
        for S in itertools.combinations(ts, j + 1):
            cls.append([-x for x in S])
        for S in itertools.combinations(ts, k - j + 1):
            cls.append(list(S))
    return var, nxt[0] - 1, cls

def solve(nv, cls, timeout=600):
    txt = f"p cnf {nv} {len(cls)}\n" + "".join(
        " ".join(map(str, c)) + " 0\n" for c in cls)
    p = subprocess.run([SAT, "-b", "cadical", "--timeout", str(timeout)],
                       input=txt, capture_output=True, text=True)
    if "s SATISFIABLE" not in p.stdout: return None
    model = set()
    for ln in p.stdout.splitlines():
        if ln.startswith("v "):
            for t in ln[2:].split():
                v = int(t)
                if v > 0: model.add(v)
    return model

def signed(A, B, G, var, model, R=49, n=4):
    out = []
    for T, kind in ((A, 'a'), (B, 'b'), (G, 'g')):
        d = []
        for m in range(R):
            e = {}
            for i in range(n):
                for j in range(n):
                    if T[m][i][j]:
                        e[(i, j)] = -1 if var[(kind, m, i, j)] in model else 1
            d.append(e)
        out.append(d)
    return out

def verify(al, be, ga, n=4, trials=5):
    rng = random.Random(11)
    for _ in range(trials):
        X = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n)]
        Y = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n)]
        want = [[sum(X[i][k]*Y[k][j] for k in range(n)) for j in range(n)]
                for i in range(n)]
        C = [[0]*n for _ in range(n)]
        for m in range(len(al)):
            u = sum(v*X[i][j] for (i, j), v in al[m].items())
            w = sum(v*Y[i][j] for (i, j), v in be[m].items())
            for (i, j), v in ga[m].items(): C[i][j] += v*u*w
        if C != want: return False
    return True

def lift(path, R=49, n=4):
    A, B, G = load(path, R, n)
    var, nv, cls = build_cnf(A, B, G, R, n)
    model = solve(nv, cls)
    if model is None: return None
    al, be, ga = signed(A, B, G, var, model, R, n)
    return (al, be, ga) if verify(al, be, ga, n) else "FAILED-VERIFY"

if __name__ == "__main__":
    r = lift(sys.argv[1])
    if r is None: print(f"{sys.argv[1]}: NO SIGN LIFT (unsat)")
    elif r == "FAILED-VERIFY": print(f"{sys.argv[1]}: LIFT FAILED VERIFICATION")
    else:
        print(f"{sys.argv[1]}: LIFTED + VERIFIED")
        if len(sys.argv) > 2:
            al, be, ga = r
            import json
            json.dump([[{f"{i},{j}": v for (i, j), v in d.items()} for d in side]
                       for side in (al, be, ga)], open(sys.argv[2], "w"))
