#!/usr/bin/env python3
"""sw_points.py: direct-sum programs for points of the <2x2x2:7> orbit, to compare them as the SW level (2026-11-22).

The library's 2x2 level runs DPS's dyadic point (schemes/opt/dps7_*, PLinOpt's 2x2x2_7_DPS-evenpow-12.2034, their
Eq. (38)).  DPS's optimum has coefficients in Q(sqrt 3) (PLinOpt's 2x2x2_7_DPS-accurate, which writes 1013 as a
placeholder for sqrt 3): amplification ratio 1.871 per level against 2.084.  This writes both points as direct sums,
every output one sum of its inputs times constants, in the one-operation-per-line syntax gen_kernels.py --sw reads:

  schemes/sw/q3_{L,R,P}.slp      the Q(sqrt 3) point, constants rounded to the nearest double
  schemes/sw/dps7d_{L,R,P}.slp   the dyadic point as direct sums: the control, same writer, exact constants

Each scheme is first checked exactly against the Brent equations (in Q(sqrt 3), numbers a + b sqrt 3 with a, b
rational), in the library's convention vec(AB) = P((L vec A) . (R vec B)), row-major; then every written program is
read back and compared with its matrix.
"""
import os, re, sys
from decimal import Decimal, getcontext
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "dps48", "plinopt", "data")
getcontext().prec = 60
SQRT3 = Decimal(3).sqrt()


class Q3:
    """a + b sqrt 3, a and b rational"""
    __slots__ = ("a", "b")
    def __init__(self, a=0, b=0): self.a, self.b = Fr(a), Fr(b)
    def __add__(self, o): return Q3(self.a + o.a, self.b + o.b)
    def __mul__(self, o): return Q3(self.a * o.a + 3 * self.b * o.b, self.a * o.b + self.b * o.a)
    def __eq__(self, o): return self.a == o.a and self.b == o.b
    def iszero(self): return self.a == 0 and self.b == 0
    def dec(self): return Decimal(self.a.numerator) / Decimal(self.a.denominator) + Decimal(self.b.numerator) / Decimal(self.b.denominator) * SQRT3
    def __repr__(self): return f"{self.a}+{self.b}r3"


def read_sms(path):
    """PLinOpt .sms -> rows x cols of Q3; with the header's placeholder, a numerator b * 1013 + a means b sqrt 3 + a"""
    sqrt3 = False
    with open(path) as f:
        head = f.readline()
        while head.startswith("#"):
            sqrt3 |= "1013 is a placeholder for sqrt(3)" in head
            head = f.readline()
        r, c, _ = head.split()
        M = [[Q3() for _ in range(int(c))] for _ in range(int(r))]
        for line in f:
            t = line.split()
            if len(t) < 3 or t[0] == "0":
                break
            num, den = (t[2].split("/") + ["1"])[:2]
            num, den = int(num), int(den)
            if sqrt3:
                b = round(num / 1013); a = num - 1013 * b
                assert abs(a) <= 10, (path, t)
                v = Q3(Fr(a, den), Fr(b, den))
            else:
                v = Q3(Fr(num, den))
            M[int(t[0]) - 1][int(t[1]) - 1] = v
    return M


def brent(L, R, P):
    """exact: sum_k L[k][(i,j)] R[k][(j',l)] P[(i',l')][k] = [j = j'][i = i'][l = l'] on 2x2 grids, row-major"""
    bad = 0
    for i in range(2):
        for j in range(2):
            for j2 in range(2):
                for l in range(2):
                    for i2 in range(2):
                        for l2 in range(2):
                            s = Q3()
                            for k in range(7):
                                s = s + L[k][2 * i + j] * R[k][2 * j2 + l] * P[2 * i2 + l2][k]
                            want = Q3(1 if (j == j2 and i == i2 and l == l2) else 0)
                            bad += not (s == want)
    return bad


def const(v):
    """the double nearest to |v|, as a C literal with a decimal point"""
    x = float(abs(v.dec()))
    s = repr(x)
    assert "e" not in s and "." in s, s
    return s


def write(path, head, M):
    """direct sums, one operation per line: products by constants first, then the sum in input order
    (a positive term first where there is one); outputs are plain copies, as gen_kernels.py's kron() wants"""
    out, n = [head], 0
    def tmp():
        nonlocal n
        n += 1
        return f"t{n}"
    outs = []
    for row in M:
        terms = []
        for i, v in enumerate(row):
            if v.iszero():
                continue
            neg = v.dec() < 0
            if abs(v.dec()) == 1:
                terms.append((neg, f"i{i}"))
            else:
                t = tmp(); out.append(f"{t}:=i{i}*{const(v)};"); terms.append((neg, t))
        terms.sort(key=lambda t: t[0])                 # stable: positive terms first, input order kept within each
        neg, acc = terms[0]
        if neg:                                        # no positive term
            t = tmp(); out.append(f"{t}:=-{acc};"); acc = t
        for neg, x in terms[1:]:
            t = tmp(); out.append(f"{t}:={acc}{'-' if neg else '+'}{x};"); acc = t
        outs.append(acc)
    out += [f"o{k}:={v};" for k, v in enumerate(outs)]
    open(path, "w").write("\n".join(out) + "\n")
    return n


LINE = re.compile(r"^(\w+):=(-?)(\w+)(?:([-+*/])(\w+|\d+\.\d+))?;$")

def readback(path, M, tol):
    """evaluate the written program on unit inputs (in 60-digit decimals); max |program - matrix|"""
    worst = Decimal(0)
    for j in range(len(M[0])):
        env = {f"i{i}": Decimal(1 if i == j else 0) for i in range(len(M[0]))}
        for ln in open(path):
            ln = ln.strip()
            if not ln or ln.startswith("#"):
                continue
            lhs, neg, a, op, b = LINE.match(ln).groups()
            va = env[a]
            if neg: va = -va
            if op:
                vb = env[b] if b in env else Decimal(b)
                va = va + vb if op == "+" else va - vb if op == "-" else va * vb if op == "*" else va / vb
            env[lhs] = va
        for k, row in enumerate(M):
            worst = max(worst, abs(env[f"o{k}"] - row[j].dec()))
    assert worst <= tol, (path, worst)
    return worst


def main():
    os.makedirs(os.path.join(HERE, "schemes", "sw"), exist_ok=True)
    for name, src, what, tol in (("q3", "2x2x2_7_DPS-accurate", "DPS's optimum in Q(sqrt 3), constants rounded to double", Decimal("4e-16")),
                                 ("dps7d", "2x2x2_7_DPS-evenpow-12.2034", "DPS's dyadic point, Eq. (38), exact constants", Decimal(0))):
        L, R, P = (read_sms(os.path.join(DATA, f"{src}_{s}.sms")) for s in "LRP")
        assert len(L) == len(R) == 7 and len(P) == 4
        bad = brent(L, R, P)
        assert bad == 0, f"{src}: {bad} Brent equations fail"
        counts = []
        for side, M, io in (("L", L, "4 blocks of A -> 7 left factors"), ("R", R, "4 blocks of B -> 7 right factors"), ("P", P, "7 products -> 4 blocks of C")):
            path = os.path.join(HERE, "schemes", "sw", f"{name}_{side}.slp")
            nt = write(path, f"# <2x2x2:7> {side} program, {what} (PLinOpt's {src}); {io}; direct sums written by sw_points.py", M)
            worst = readback(path, M, tol)
            counts.append(f"{side} {nt} operations, readback {float(worst):.1e}")
        amp2 = max(sum(float((P[o][k].dec()) ** 2) * sum(float(v.dec()) ** 2 for v in L[k]) * sum(float(v.dec()) ** 2 for v in R[k]) for k in range(7)) for o in range(4))
        print(f"{name}: 64 Brent equations exact; amplification {0.5 * amp2 ** 0.5:.4f} (ratio {amp2 ** 0.5 / 2 ** 0.5:.4f}); " + "; ".join(counts))


if __name__ == "__main__":
    main()
