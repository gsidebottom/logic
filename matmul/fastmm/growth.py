"""Growth factors of bilinear matrix-multiplication schemes, as defined in Dumas, Pernet,
Sedoglavic, arXiv:2603.18699v3, eq. (4) and (5):

  gamma_{p,q} = || ( sum_i ||L_i,*||_{q*} ||R_i,*||_{q*} |P_j,i| )_j ||_p     (q* the dual of q)
  gamma_2     = sum_i ||L_i,*||_2 ||R_i,*||_2 ||P_*,i||_2

Schemes are read from straight-line programs (PLinOpt .slp: inputs i<k>, outputs o<k>) by
evaluating them as linear maps over the rationals, or from PLinOpt .sms matrices; each is
checked against the matrix multiplication tensor (Brent equations) before use."""
import math, os, re, sys
from fractions import Fraction as F

def parse_slp(text, nin):
    env = {}
    stmts = [s.strip() for s in re.split(r"[;\n]", text) if s.strip()]
    outs = {}
    for s in stmts:
        name, expr = s.split(":=")
        toks = re.findall(r"\d+\.\d+|\d+/\d+|\d+|[A-Za-z_]\w*|[-+*/()]", expr)
        assert "".join(toks) == expr.replace(" ", ""), f"unparsed characters in {s}"
        pos = [0]
        def peek():
            return toks[pos[0]] if pos[0] < len(toks) else None
        def take():
            pos[0] += 1
            return toks[pos[0] - 1]
        def add(a, b, sgn=1):
            r = dict(a)
            for k, v in b.items():
                r[k] = r.get(k, 0) + sgn * v
            return {k: v for k, v in r.items() if v != 0}
        def scale(a, c):
            return {k: v * c for k, v in a.items() if v * c != 0}
        def const(a):
            assert set(a) <= {"1"}, f"nonlinear term in {s}"
            return a.get("1", F(0))
        def atom():
            t = take()
            if t == "(":
                v = expr_()
                assert take() == ")"
                return v
            if t == "-":
                return scale(atom(), -1)
            if re.fullmatch(r"\d+\.\d+|\d+/\d+|\d+", t):
                return {"1": F(t)}
            if re.fullmatch(r"i\d+", t):
                return {int(t[1:]): F(1)}
            return dict(env[t])
        def term():
            v = atom()
            while peek() in ("*", "/"):
                op = take()
                w = atom()
                if op == "*":
                    v = scale(v, const(w)) if set(w) <= {"1"} else scale(w, const(v))
                else:
                    v = scale(v, 1 / const(w))
            return v
        def expr_():
            v = term()
            while peek() in ("+", "-"):
                op = take()
                v = add(v, term(), 1 if op == "+" else -1)
            return v
        val = expr_()
        assert pos[0] == len(toks), f"trailing tokens in {s}"
        env[name.strip()] = val
        if re.fullmatch(r"o\d+", name.strip()):
            outs[int(name.strip()[1:])] = val
    nout = max(outs) + 1
    M = [[F(0)] * nin for _ in range(nout)]
    for o, v in outs.items():
        for k, c in v.items():
            assert k != "1", "constant term"
            M[o][k] = c
    return M

def parse_sms(path):
    lines = [ln for ln in open(path).read().split("\n") if ln.strip() and not ln.lstrip().startswith("#")]
    r, c, _ = lines[0].split()
    M = [[F(0)] * int(c) for _ in range(int(r))]
    for ln in lines[1:]:
        f = ln.split()
        if len(f) < 3 or f[0] == "0":
            continue
        M[int(f[0]) - 1][int(f[1]) - 1] = F(f[2])
    return M

def check_scheme(L, R, P, m, k, n):
    """P ((L vec A) . (R vec B)) = vec(A B) for row-major vec, all entries exactly"""
    r = len(L)
    assert len(R) == r and len(P[0]) == r and len(L[0]) == m * k and len(R[0]) == k * n and len(P) == m * n
    for a in range(m * k):
        for b in range(k * n):
            la = [L[i][a] for i in range(r)]
            rb = [R[i][b] for i in range(r)]
            lr = [la[i] * rb[i] for i in range(r)]
            if not any(lr):
                continue
            for c in range(m * n):
                t = sum(P[c][i] * lr[i] for i in range(r) if lr[i])
                i1, j1 = divmod(a, k)
                j2, l2 = divmod(b, n)
                i3, l3 = divmod(c, n)
                want = 1 if (j1 == j2 and i1 == i3 and l2 == l3) else 0
                if t != want:
                    return False
    # also the terms with lr == 0 must give 0 everywhere: covered (sum over empty is 0) except
    # a pair (a, b) that the product needs but no product touches
    for i1 in range(m):
        for j in range(k):
            for l in range(n):
                a, b = i1 * k + j, j * n + l
                if not any(L[i][a] * R[i][b] for i in range(r)):
                    return False
    return True

def norm(v, p):
    v = [abs(float(x)) for x in v]
    return max(v) if p == "inf" else math.sqrt(sum(x * x for x in v)) if p == 2 else sum(v)

def gammas(L, R, P):
    r = len(L)
    out = {}
    for p, q in [("inf", "inf"), ("inf", 2), (2, "inf"), (2, 2)]:
        qs = 1 if q == "inf" else 2
        w = [norm(L[i], qs) * norm(R[i], qs) for i in range(r)]
        v = [sum(w[i] * abs(float(P[j][i])) for i in range(r)) for j in range(len(P))]
        out[(p, q)] = norm(v, p)
    out["g2"] = sum(norm(L[i], 2) * norm(R[i], 2) * norm([P[j][i] for j in range(len(P))], 2) for i in range(r))
    return out



def from_slp(prefix, mm, r):
    t = [open(f"{prefix}_{s}.slp").read() for s in "LRP"]
    return parse_slp(t[0], mm), parse_slp(t[1], mm), parse_slp(t[2], r)


def from_sms(prefix):
    return tuple(parse_sms(f"{prefix}_{s}.sms") for s in "LRP")


def known_schemes():
    """the schemes of the fast-matmul library and the paper's comparison"""
    here = os.path.dirname(os.path.abspath(__file__))
    data = os.path.join(here, "..", "dps48", "plinopt", "data")
    gk = open(os.path.join(here, "gen_kernels.py")).read()
    sw = [re.search(rf'SW_{s} = """(.*?)"""', gk, re.S).group(1) for s in "LRP"]
    return [
        ("2x2 our SW kernels (gen_kernels.py)", 2, (parse_slp(sw[0], 4), parse_slp(sw[1], 4), parse_slp(sw[2], 7))),
        ("2x2 Winograd (PLinOpt)", 2, from_sms(f"{data}/2x2x2_7_Winograd")),
        ("2x2 Strassen (PLinOpt)", 2, from_sms(f"{data}/2x2x2_7_Strassen")),
        ("4x4 DPS25 rational, .sms", 4, from_sms(f"{data}/4x4x4_48_rational")),
        ("4x4 DPS25 rational, .slp (315 ops)", 4, from_slp(f"{data}/4x4x4_48_rational", 16, 48)),
        ("4x4 Table 1 accurate, .sms", 4, from_sms(f"{data}/4x4x4_48_accurate")),
        ("4x4 Table 1 accurate, .slp (our D48 kernels)", 4, from_slp(f"{data}/4x4x4_48_accurate", 16, 48)),
        ("4x4 our 201-op point, .slp", 4, from_slp(os.path.join(here, "..", "dps48", "cand48", "p005_201n"), 16, 48)),
        ("4x4x4:49 156 (PLinOpt)", 4, from_sms(f"{data}/4x4x4_49_156")),
    ]


if __name__ == "__main__":
    # growth.py                 the known schemes
    # growth.py PREFIX k r      a <k x k x k : r> scheme from PREFIX_{L,R,P}.slp (else .sms)
    if len(sys.argv) > 1:
        prefix, k, r = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
        L, R, P = from_slp(prefix, k * k, r) if os.path.exists(prefix + "_L.slp") else from_sms(prefix)
        schemes = [(os.path.basename(prefix), k, (L, R, P))]
    else:
        schemes = known_schemes()
    print(f"{'scheme':<46} {'exact':>5} {'g(inf,inf)':>11} {'g(inf,2)':>9} {'g(2,inf)':>9} {'g(2,2)':>8} {'gamma2':>8}"
          "   exponents log_k g: (inf,inf) (inf,2) (2,inf) (2,2)")
    for name, k, (L, R, P) in schemes:
        ok = check_scheme(L, R, P, k, k, k)
        g = gammas(L, R, P)
        ex = [math.log(g[x], k) for x in [("inf", "inf"), ("inf", 2), (2, "inf"), (2, 2)]]
        print(f"{name:<46} {'yes' if ok else 'NO':>5} {g[('inf', 'inf')]:11.3f} {g[('inf', 2)]:9.3f} {g[(2, 'inf')]:9.3f}"
              f" {g[(2, 2)]:8.3f} {g['g2']:8.3f}   " + "  ".join(f"{e:.3f}" for e in ex))
