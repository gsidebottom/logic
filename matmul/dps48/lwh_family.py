#!/usr/bin/env python3
"""The Li-Wang-Hu one-parameter family of rank-48 schemes (arXiv:2607.15069, Appendix A).

Li, Wang and Hu show that the Dumas-Pernet-Sedoglavic rational solution lies on a curve
s(t) of rank-48 decompositions of <4,4,4> with coefficients rational in t, and that
their invariant phi(s(t)) = 64 + 4/t^2 + 1024 t^2 separates the isotropy classes for
t in [1/4, oo).  This module reads the 48 layers (U_i(t), V_i(t), W_i(t)) from the
paper's TeX source (data only: entries are parsed with a restricted evaluator, nothing
from the file is executed), verifies the family, writes members as PLinOpt sms triples,
and computes the invariant on any scheme.

  lwh_family.py verify TEX              exact Brent check of s(t) as an identity in Q(t)
  lwh_family.py sms TEX T OUTPREFIX     write OUTPREFIX_{L,R,P}.sms for t = T (e.g. 1/4)
  lwh_family.py phi PREFIX              invariant of the scheme PREFIX_{L,R,P}.sms and the
                                        t >= 1/4 it corresponds to

Conventions are ours: vec(AB) = P((L vecA) o (R vecB)), row-major, row k of L = vec U_k,
row k of R = vec V_k, column k of P = vec of the output factor (W_k or its transpose,
whichever the Brent check accepts).
"""
import ast
import itertools
import math
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import slp48check as C  # noqa: E402

# ------------------------------------------------------------------ parsing the TeX
def tex_to_expr(s):
    """LaTeX entry -> arithmetic expression string in t."""
    s = s.strip().replace(r"\,", "").replace(" ", "")
    s = s.replace(r"\dfrac", r"\tfrac").replace(r"\frac", r"\tfrac")
    # innermost-first replacement of \tfrac{A}{B} by ((A)/(B))
    pat = re.compile(r"\\tfrac\{([^{}]*)\}\{([^{}]*)\}")
    while True:
        s2 = pat.sub(r"((\1)/(\2))", s)
        if s2 == s:
            break
        s = s2
    assert "\\" not in s and "{" not in s, f"unparsed TeX in entry: {s!r}"
    # implicit multiplication: 4t, 2(, )(, t(, )t, )4
    s = re.sub(r"(\d)(t|\()", r"\1*\2", s)
    s = re.sub(r"(t|\))(\d|t|\()", r"\1*\2", s)
    return s


_ALLOWED = (ast.Expression, ast.BinOp, ast.UnaryOp, ast.Constant, ast.Name, ast.Load,
            ast.Add, ast.Sub, ast.Mult, ast.Div, ast.USub, ast.UAdd)


def evaluate(expr, t):
    """exact value of an entry expression at t (a Fraction); only + - * / and t allowed."""
    tree = ast.parse(expr, mode="eval")
    for node in ast.walk(tree):
        if not isinstance(node, _ALLOWED):
            raise ValueError(f"disallowed syntax {type(node).__name__} in {expr!r}")
        if isinstance(node, ast.Name) and node.id != "t":
            raise ValueError(f"unknown name {node.id!r} in {expr!r}")
        if isinstance(node, ast.Constant) and not isinstance(node.value, int):
            raise ValueError(f"non-integer constant in {expr!r}")

    def ev(n):
        if isinstance(n, ast.Expression):
            return ev(n.body)
        if isinstance(n, ast.Constant):
            return Fr(n.value)
        if isinstance(n, ast.Name):
            return Fr(t)
        if isinstance(n, ast.UnaryOp):
            v = ev(n.operand)
            return -v if isinstance(n.op, ast.USub) else v
        a, b = ev(n.left), ev(n.right)
        if isinstance(n.op, ast.Add):
            return a + b
        if isinstance(n.op, ast.Sub):
            return a - b
        if isinstance(n.op, ast.Mult):
            return a * b
        return a / b

    return ev(tree)


def parse(tex_path):
    """-> list of 48 layers, each (U, V, W) as 4x4 lists of expression strings."""
    text = open(tex_path).read()
    start = text.index(r"\label{sec-app}")
    app = text[start:]
    blocks = re.split(r"\$i=(\d+)\$", app)
    # blocks: [preamble, '1', body1, '2', body2, ...]
    layers = []
    for k in range(1, len(blocks), 2):
        idx, body = int(blocks[k]), blocks[k + 1]
        mats = re.findall(r"\\begin\{matrix\}(.*?)\\end\{matrix\}", body, re.S)
        assert len(mats) >= 3, f"layer {idx}: {len(mats)} matrices"
        triple = []
        for m in mats[:3]:
            rows = [r for r in (x.strip() for x in m.split(r"\\")) if r]
            assert len(rows) == 4, f"layer {idx}: {len(rows)} rows"
            mat = []
            for r in rows:
                ents = [e.strip() for e in r.split("&")]
                assert len(ents) == 4, f"layer {idx}: row {r!r}"
                mat.append([tex_to_expr(e) for e in ents])
            triple.append(mat)
        layers.append((idx, triple))
    assert [i for i, _ in layers] == list(range(1, 49)), "layers not numbered 1..48"
    return [tr for _, tr in layers]


def scheme(layers, t):
    """(U, V, W) at t: lists of 48 4x4 Fraction matrices."""
    out = ([], [], [])
    for tri in layers:
        for f in range(3):
            out[f].append([[evaluate(e, t) for e in row] for row in tri[f]])
    return out


def to_lrp(U, V, W, transpose_w):
    L = [[U[k][i][j] for i in range(4) for j in range(4)] for k in range(48)]
    R = [[V[k][i][j] for i in range(4) for j in range(4)] for k in range(48)]
    Wf = [[[W[k][j][i] for j in range(4)] for i in range(4)] if transpose_w else W[k] for k in range(48)]
    P = [[Wf[k][c // 4][c % 4] for k in range(48)] for c in range(16)]
    return L, R, P


def find_convention(layers, t=Fr(1, 2)):
    U, V, W = scheme(layers, t)
    for tw in (False, True):
        if C.brent(*to_lrp(U, V, W, tw)) == 0:
            return tw
    return None


# ------------------------------------------------------------------ invariant
def det4(M):
    """exact determinant (Bareiss-free Laplace on 4x4 is fine for Fractions)."""
    def det(m):
        if len(m) == 1:
            return m[0][0]
        s = Fr(0)
        for j, a in enumerate(m[0]):
            if a:
                minor = [row[:j] + row[j + 1:] for row in m[1:]]
                s += (-1) ** j * a * det(minor)
        return s
    return det(M)


def rank(M):
    m = [row[:] for row in M]
    r = 0
    for c in range(len(m[0])):
        p = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def mixed(mats):
    """coefficient of x1 x2 x3 x4 in det(sum x_j A_j), by inclusion-exclusion."""
    s = Fr(0)
    for size in range(1, 5):
        for S in itertools.combinations(range(4), size):
            A = [[sum(mats[j][r][c] for j in S) for c in range(4)] for r in range(4)]
            s += (-1) ** (4 - size) * det4(A)
    return s


def phi(U, V, W):
    """Li-Wang-Hu invariant: sum over 4-subsets H of the rank-(2,2,2) layers of
    C(U,H) C(V,H) C(W,H).  Returns (phi, the rank-2 layer list, rank-triple census)."""
    triples = [(rank(U[k]), rank(V[k]), rank(W[k])) for k in range(48)]
    census = {}
    for tr in triples:
        census[tr] = census.get(tr, 0) + 1
    R2 = [k for k in range(48) if triples[k] == (2, 2, 2)]
    total = Fr(0)
    for H in itertools.combinations(R2, 4):
        cu = mixed([U[k] for k in H])
        if cu == 0:
            continue
        cv = mixed([V[k] for k in H])
        if cv == 0:
            continue
        total += cu * cv * mixed([W[k] for k in H])
    return total, R2, census


def t_from_phi(ph):
    """t >= 1/4 with 64 + 4/t^2 + 1024 t^2 = phi (None if no real solution)."""
    a = Fr(ph) - 64  # 1024 t^4 - a t^2 + 4 = 0
    disc = a * a - 16384
    if disc < 0:
        return None
    t2 = (float(a) + math.sqrt(float(disc))) / 2048
    return math.sqrt(t2)


def read_lrp(prefix):
    L = C_read(prefix + "_L.sms")
    R = C_read(prefix + "_R.sms")
    P = C_read(prefix + "_P.sms")
    U = [[[L[k][4 * i + j] for j in range(4)] for i in range(4)] for k in range(48)]
    V = [[[R[k][4 * i + j] for j in range(4)] for i in range(4)] for k in range(48)]
    W = [[[P[4 * i + j][k] for j in range(4)] for i in range(4)] for k in range(48)]
    return U, V, W


def C_read(path):
    M = None
    for ln in open(path):
        p = ln.split()
        if M is None:
            if len(p) >= 2 and p[0].isdigit() and p[1].isdigit():
                M = [[Fr(0)] * int(p[1]) for _ in range(int(p[0]))]
            continue
        if len(p) < 3 or (p[0] == "0" and p[1] == "0"):
            break
        M[int(p[0]) - 1][int(p[1]) - 1] = Fr(p[2])
    return M


def write_sms(path, M):
    rows, cols = len(M), len(M[0])
    with open(path, "w") as f:
        f.write(f"{rows} {cols} R\n")
        for i in range(rows):
            for j in range(cols):
                if M[i][j] != 0:
                    f.write(f"{i + 1} {j + 1} {M[i][j]}\n")
        f.write("0 0 0\n")


# ------------------------------------------------------------------ main
def main():
    cmd = sys.argv[1]
    if cmd == "verify":
        layers = parse(sys.argv[2])
        tw = find_convention(layers)
        assert tw is not None, "neither output convention satisfies the Brent equations at t = 1/2"
        print(f"output factor convention: {'W transposed' if tw else 'W as given'}")
        # each entry is (p + q t)/(2^a t^k), k <= 1, so each Brent equation is a Laurent
        # polynomial in t with exponents in [-3, 3]: agreement at 9 distinct t proves it
        ts = [Fr(1, 4), Fr(1, 2), Fr(1), Fr(2), Fr(4), Fr(8), Fr(3), Fr(-5, 7), Fr(11, 3)]
        degs = set()
        for tri in [l for l in layers]:
            for m in tri:
                for row in m:
                    for e in row:
                        degs.add(e.count("t"))
        for t in ts:
            bad = C.brent(*to_lrp(*scheme(layers, t), tw))
            print(f"  t = {t}: {4096 - bad}/4096 Brent equations hold")
            assert bad == 0
        print(f"identity in Q(t) verified (9 points; max t-occurrences per entry {max(degs)})")
        for t in (Fr(1, 2), Fr(1, 4), Fr(2)):
            ph, R2, census = phi(*scheme(layers, t))
            want = 64 + Fr(4) / (t * t) + 1024 * t * t
            print(f"  phi(s({t})) = {ph}  (paper: {want}) {'OK' if ph == want else 'MISMATCH'}; "
                  f"rank-2 layers {[k + 1 for k in R2]}; census {census}")
    elif cmd == "sms":
        layers = parse(sys.argv[2])
        t = Fr(sys.argv[3])
        tw = find_convention(layers)
        L, R, P = to_lrp(*scheme(layers, t), tw)
        assert C.brent(L, R, P) == 0
        for name, M in (("L", L), ("R", R), ("P", P)):
            write_sms(f"{sys.argv[4]}_{name}.sms", M)
        vals = sorted({abs(x) for M in (L, R, P) for row in M for x in row if x})
        print(f"wrote {sys.argv[4]}_{{L,R,P}}.sms for t = {t}: Brent 4096/4096; |coefficients| {[str(v) for v in vals]}")
    elif cmd == "phi":
        U, V, W = read_lrp(sys.argv[2])
        ph, R2, census = phi(U, V, W)
        print(f"phi = {ph} (= {float(ph):.6f}); rank-triple census {census}; t >= 1/4 with this phi: {t_from_phi(ph)}")
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
