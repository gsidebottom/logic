"""A first-order rounding-error model of one recursion level of a <4x4x4:48> program: the L, R and
P straight-line programs (PLinOpt syntax, as gen_kernels.py fuses them) evaluated as written, left
to right within each line.

Every addition, and every scaling by a constant that is not a power of two, rounds; its error has
variance proportional to E[v^2], v the exact value rounded, and the errors are independent.  The
inputs are i.i.d. with unit variance, so the products M_i = X_i Y_i have covariance
G_ii' = (L_i.L_i')(R_i.R_i') and every E[v^2], cancellation included, is an exact second moment.
Propagating each rounding to the outputs gives the RMS error the passes add to one level, relative
to the RMS of an output (2), in units of the per-rounding standard deviation:

  L+R      errors of the block combinations X_i, Y_i, carried through the products and P
  P        errors of the output pass
  worst    all passes, the worst output
  amp      sqrt(sum_i p_ji^2 G_ii) / 2 for the worst output: how much the leaf products' own
           (recursive) errors are amplified per level; a property of the scheme
  count    roundings of the P pass that reach an output, mean over the outputs
  size     their RMS size in output units (value times its weight in the output), mean over the
           outputs; the P error of an output is sqrt(count) * size
  chain    the longest chain of roundings from an input to an output of one level

  python3 slp_errmodel.py NAME PREFIX [NAME PREFIX ...]     PREFIX_{L,R,P}.slp
"""
import re
import sys
from fractions import Fraction
import numpy as np
np.seterr(all="ignore")     # Accelerate's matmul raises spurious flags

TOK = re.compile(r"\s*(?:(\d+\.\d*(?:e-?\d+)?|\d+)|([A-Za-z_]\w*)|(.))")
NUM = re.compile(r"\d+\.\d*(?:e-?\d+)?|\d+")

def is_pow2(c):
    c = abs(Fraction(c))
    return c != 0 and (c.numerator == 1 or c.denominator == 1) and \
        c.numerator & (c.numerator - 1) == 0 and c.denominator & (c.denominator - 1) == 0

class Val:
    """c: coefficients over the inputs; w: {rounding: weight} (first-order error terms);
    d: {input: longest chain of roundings from it}"""
    __slots__ = ("c", "w", "d")
    def __init__(self, c, w, d):
        self.c, self.w, self.d = c, w, d

class Program:
    def __init__(self, path, nin):
        self.nin, self.rounded, self.env = nin, [], {}
        for line in open(path):
            line = line.strip()
            if not line or line.startswith("#") or ":=" not in line:
                continue
            lhs, rhs = line.rstrip(";").split(":=", 1)
            self.toks = [a or b or c for a, b, c in TOK.findall(rhs) if (a or b or c).strip()]
            self.k = 0
            self.env[lhs.strip()] = self.expr()

    def peek(self):
        return self.toks[self.k] if self.k < len(self.toks) else None

    def eat(self):
        self.k += 1
        return self.toks[self.k - 1]

    def rounding(self, c, w, d):
        self.rounded.append(c.copy())
        w = dict(w)
        w[len(self.rounded) - 1] = 1.0
        return Val(c, w, {x: n + 1 for x, n in d.items()})

    def expr(self):
        v = self.term()
        while self.peek() in ("+", "-"):
            s = 1.0 if self.eat() == "+" else -1.0
            u = self.term()
            w = dict(v.w)
            for r, x in u.w.items():
                w[r] = w.get(r, 0.0) + s * x
            d = dict(v.d)
            for x, n in u.d.items():
                d[x] = max(d.get(x, 0), n)
            v = self.rounding(v.c + s * u.c, w, d)
        return v

    def term(self):
        v = self.factor()
        while self.peek() in ("*", "/"):
            op = self.eat()
            u = self.factor()
            if isinstance(u, Fraction):
                v = self.scale(v, u if op == "*" else 1 / u)
            elif isinstance(v, Fraction) and op == "*":
                v = self.scale(u, v)
            else:
                raise ValueError("not a linear program")
        return v

    def scale(self, v, c):
        if isinstance(v, Fraction):
            return v * c
        f = float(c)
        out = Val(v.c * f, {r: x * f for r, x in v.w.items()}, dict(v.d))
        return out if is_pow2(c) else self.rounding(out.c, out.w, out.d)

    def factor(self):
        tok = self.eat()
        if tok == "-":
            v = self.factor()
            return -v if isinstance(v, Fraction) else Val(-v.c, {r: -x for r, x in v.w.items()}, v.d)
        if tok == "(":
            v = self.expr()
            assert self.eat() == ")"
            return v
        if NUM.fullmatch(tok):
            return Fraction(tok)
        if tok in self.env:
            v = self.env[tok]
            return Val(v.c.copy(), dict(v.w), dict(v.d))
        e = np.zeros(self.nin)
        e[int(re.fullmatch(r"i(\d+)", tok).group(1))] = 1.0
        return Val(e, {}, {int(tok[1:]): 0})

    def outputs(self, n):
        vs = [self.env[f"o{j}"] for j in range(n)]
        W = np.zeros((n, len(self.rounded)))
        for j, v in enumerate(vs):
            for r, x in v.w.items():
                W[j, r] = x
        return np.array([v.c for v in vs]), W, np.array(self.rounded), [v.d for v in vs]

def analyse(prefix):
    L, WL, NL, dL = Program(f"{prefix}_L.slp", 16).outputs(48)
    R, WR, NR, dR = Program(f"{prefix}_R.slp", 16).outputs(48)
    P, WP, NP, dP = Program(f"{prefix}_P.slp", 48).outputs(16)
    GL, GR = L @ L.T, R @ R.T
    G = GL * GR
    assert np.allclose(np.einsum("ji,il,jl->j", P, G, P), 4.0), "not a <4x4x4:48> scheme"
    covX = (WL * (NL ** 2).sum(1)) @ WL.T          # rounding-error covariance of X = L a
    covY = (WR * (NR ** 2).sum(1)) @ WR.T
    lr = np.einsum("ji,jk,ik->j", P, P, covX * GR + GL * covY)
    size2 = np.einsum("ki,il,kl->k", NP, G, NP)    # E[v^2] of each rounded value of the P pass
    p = (WP ** 2 * size2).sum(1)
    amp = np.sqrt((P ** 2 * np.diag(G)).sum(1)) / 2
    count = (np.abs(WP) > 1e-12).sum(1)
    size = np.sqrt((WP ** 2 * size2).sum(1) / 4 / count)
    depthL = [max(d.values()) for d in dL]
    depthR = [max(d.values()) for d in dR]
    chain = max(depthL[i] + depthR[i] + n for d in dP for i, n in d.items())
    rel = lambda v: np.sqrt(v / 4)
    return dict(lr=rel(lr).mean(), p=rel(p).mean(), worst=rel(lr + p).max(), amp=amp.max(),
                count=count.mean(), size=size.mean(), chain=chain,
                roundings=(len(NL), len(NR), len(NP)))

if __name__ == "__main__":
    print(f"{'program':34s} {'L+R':>5s} {'P':>5s} {'worst':>6s} {'amp':>5s}   count  size   chain   roundings L/R/P")
    for name, prefix in zip(sys.argv[1::2], sys.argv[2::2]):
        a = analyse(prefix)
        print(f"{name:34s} {a['lr']:5.2f} {a['p']:5.2f} {a['worst']:6.2f} {a['amp']:5.2f}   "
              f"{a['count']:5.1f} {a['size']:5.2f}    {a['chain']:3d}    {'/'.join(map(str, a['roundings']))}")
