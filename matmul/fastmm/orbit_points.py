#!/usr/bin/env python3
"""orbit_points.py: other points of the <3x6x3:40> orbit as the R363 level, without dense programs (2026-11-22).

A point of a scheme's orbit under GL_g1 x GL_g2 x GL_g3 is the scheme run on transformed grids: with
A' = U^-1 A V and B' = V^-1 B W it computes C' = A'B' = U^-1 (AB) W, and C = U C' W^-1.  So its programs are the
base scheme's programs with the input blocks mixed before them and the output blocks mixed after them, and stay as
sparse as the base scheme's however dense the transformed matrices are.

DPS's accurate <3x6x3:40> point has amplification ratio 2.5495 (six of its nine outputs at 2.55, three at 1.44);
the minimum over the orbit is 2.2423, all nine outputs equal, and two 3 x 3 rotations reach it (U on the row blocks of
A and C, W on the column blocks of B and C; V, the 6 x 6 side, does not help).  This writes, into schemes/NAME/ (with
the other levels' programs copied from schemes/opt/, as gen_kernels.py --rschemes wants):

  r363h   U = W = H = (2/3) J - I, the reflection through (1, 1, 1): rational, its own inverse, six operations per
          triple of blocks; amplification ratio 2.2785, gamma_inf,2 / 6 = 4.22 (DPS's point: 5.50)
  r363m   the rotations U, W of a numerical minimizer (schemes/r363m/uw.json), 2.2423

Each written scheme is read back: its three programs are evaluated to matrices, the Brent equations checked (to
rounding: the constants are doubles) and the amplification recomputed.
"""
import json, math, os, re, shutil, sys
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
G1, G2, G3, RANK = 3, 6, 3, 40
BASE = os.path.join(HERE, "schemes", "opt")


def inverse(M):
    """the inverse of a matrix of doubles, exact in rationals, rounded to doubles"""
    n = len(M)
    a = [[Fr(float(x)) for x in row] + [Fr(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(a[r][c]))
        a[c], a[p] = a[p], a[c]
        a[c] = [x / a[c][c] for x in a[c]]
        for r in range(n):
            if r != c and a[r][c] != 0:
                a[r] = [x - a[r][c] * y for x, y in zip(a[r], a[c])]
    return np.array([[float(x) for x in row[n:]] for row in a])


def combo(terms):
    """a linear combination as program text: terms (coefficient, name); exact 0 dropped, +-1 without a product"""
    s = ""
    for c, name in terms:
        if c == 0:
            continue
        mag = "" if abs(c) == 1 else f"*{abs(float(c))!r}"
        assert "e" not in mag, mag
        s += ("-" if c < 0 else ("+" if s else "")) + name + mag
    assert s, "an empty combination"
    return s


def mix3(out, ins, M, H):
    """lines for out[a] = sum_b M[a][b] ins[b] over a triple; H: M = (2/3) J - I as a sum, a scaling and three differences"""
    if H:
        tmp = "q" + out[0]          # not o<digits>...: the kernel generator reads names starting with o as outputs
        return [f"{tmp}:=({ins[0]}+{ins[1]}+{ins[2]})*{2 / 3!r};"] + [f"{out[a]}:={tmp}-{ins[a]};" for a in range(3)]
    return [f"{out[a]}:={combo([(M[a][b], ins[b]) for b in range(3)])};" for a in range(3)]


def programs(U, W, H):
    """the three programs of the point (U, I, W) around the base programs"""
    Ui, Wi = (U, W) if H else (inverse(U), inverse(W))
    base = {s: open(os.path.join(BASE, f"r363_{s}.slp")).read() for s in "LRP"}
    body = lambda t: [ln for ln in t.splitlines() if ln.strip() and not ln.startswith("#")]
    for t in base.values():
        assert not re.search(r"\b(ma|mb|pc|pt|qma|qmb|qpt|qo)\d", t), "the base programs use this script's names"
    # L: A' = U^-1 A; the blocks of A are i{6 i + j}
    L = []
    for j in range(G2):
        L += mix3([f"ma{6 * i + j}" for i in range(3)], [f"i{6 * i + j}" for i in range(3)], Ui, H)
    L += [re.sub(r"\bi(\d+)\b", r"ma\1", ln) for ln in body(base["L"])]
    # R: B' = B W; the blocks of B are i{3 j + l}; B'_{jl} = sum_l' B_{jl'} W_{l'l}
    R = []
    for j in range(G2):
        R += mix3([f"mb{3 * j + l}" for l in range(3)], [f"i{3 * j + l}" for l in range(3)], W.T, H)
    R += [re.sub(r"\bi(\d+)\b", r"mb\1", ln) for ln in body(base["R"])]
    # P: C = U C' W^-1; the base program's outputs become pc{3 i + l}
    P = [re.sub(r"\bo(\d+)\b", r"pc\1", ln) for ln in body(base["P"])]
    for l in range(G3):
        P += mix3([f"pt{3 * i + l}" for i in range(3)], [f"pc{3 * i + l}" for i in range(3)], U, H)
    for i in range(G1):
        P += mix3([f"o{3 * i + l}" for l in range(3)], [f"pt{3 * i + l}" for l in range(3)], Wi.T, H)
    return {"L": L, "R": R, "P": P}


def matrix(lines, nin, nout):
    """the matrix a program computes: evaluated on the unit vectors"""
    env = {f"i{k}": np.eye(nin)[k] for k in range(nin)}
    for ln in lines:
        lhs, expr = ln.rstrip(";").split(":=", 1)
        assert re.fullmatch(r"[\w+\-*/(). ]+", expr), expr
        env[lhs] = eval(expr, {"__builtins__": {}}, env)
    return np.array([env[f"o{k}"] for k in range(nout)])


def check(progs):
    L = matrix(progs["L"], G1 * G2, RANK)
    R = matrix(progs["R"], G2 * G3, RANK)
    P = matrix(progs["P"], RANK, G1 * G3)
    T = np.einsum("ka,kb,ck->abc", L, R, P)                    # coefficient of A_a B_b in C_c
    want = np.zeros_like(T)
    for i in range(G1):
        for j in range(G2):
            for l in range(G3):
                want[G2 * i + j, G3 * j + l, G3 * i + l] = 1
    l2, r2 = np.linalg.norm(L, axis=1), np.linalg.norm(R, axis=1)
    per = 0.5 * np.sqrt((P ** 2) @ (l2 ** 2 * r2 ** 2)) / (0.5 * math.sqrt(G2))
    ginf = (np.abs(P) @ (l2 * r2)).max() / G2
    ops = sum(len(re.findall(r"[-+*/]", ln.split(":=", 1)[1])) for s in "LRP" for ln in progs[s])
    return float(np.abs(T - want).max()), per, float(ginf), ops


def write(name, U, W, H, what):
    d = os.path.join(HERE, "schemes", name)
    os.makedirs(d, exist_ok=True)
    for f in os.listdir(BASE):
        if f.endswith(".slp") and not f.startswith("r363_"):
            shutil.copy(os.path.join(BASE, f), os.path.join(d, f))
    progs = programs(U, W, H)
    res, per, ginf, ops = check(progs)
    assert res < 1e-14, f"{name}: Brent residual {res}"
    for s, io in (("L", "18 blocks of A -> 40 left factors"), ("R", "18 blocks of B -> 40 right factors"), ("P", "40 products -> 9 blocks of C")):
        open(os.path.join(d, f"r363_{s}.slp"), "w").write(
            f"# r363 {s}: DPS's accurate <3x6x3:40> at another point of its orbit, {what}; {io}; schemes/opt/r363_{s}.slp with the "
            f"blocks mixed around it, written by orbit_points.py\n" + "\n".join(progs[s]) + "\n")
    print(f"{name}: Brent residual {res:.1e}; amplification ratio {per.max():.4f} (outputs {per.min():.3f} to {per.max():.3f}); "
          f"gamma_inf,2 / g2 {ginf:.3f}; {ops} operations in the three programs")


def main():
    base = {s: [ln for ln in open(os.path.join(BASE, f"r363_{s}.slp")).read().splitlines() if ln.strip() and not ln.startswith("#")] for s in "LRP"}
    res, per, ginf, ops = check(base)
    print(f"schemes/opt (DPS's point): Brent residual {res:.1e}; amplification ratio {per.max():.4f} (outputs {per.min():.3f} to {per.max():.3f}); "
          f"gamma_inf,2 / g2 {ginf:.3f}; {ops} operations in the three programs")
    Hm = 2 / 3 * np.ones((3, 3)) - np.eye(3)
    write("r363h", Hm, Hm, True, "U = W = (2/3) J - I, the reflection through (1, 1, 1)")
    uw = json.load(open(os.path.join(HERE, "schemes", "r363m", "uw.json")))
    write("r363m", np.array(uw["U"]), np.array(uw["W"]), False, "the rotations U, W of schemes/r363m/uw.json, a numerical minimizer of the amplification")


if __name__ == "__main__":
    main()
