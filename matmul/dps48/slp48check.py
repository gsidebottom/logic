#!/usr/bin/env python3
"""Independent exact check of a 4x4 rank-r L/R/P program triple over Q, with
operation counts in PLinOpt's model (additions + scalings; copies and
negations free) and in Patel's model (negations also charged), and a
translation of Patel-style programs to the syntax PLinOpt's SLPchecker
accepts (`a*(1/2)` -> `a/2`, `a*(-2)` -> `-a*2`, ...).

Conventions (PLinOpt data layout, shared by Patel's files): L and R have
inputs i0..i15 = vec(A), vec(B) row-major and outputs o0..o(r-1); P has
inputs i0..i(r-1) = the products L_k * R_k and outputs o0..o15 = vec(C).

Usage: slp48check.py PREFIX            (PREFIX_L.slp, PREFIX_R.slp, PREFIX_P.slp)
       slp48check.py --dir DIR         (DIR/L.slp, DIR/R.slp, DIR/P.slp, Patel's layout)
       slp48check.py --emit-plinopt IN.slp OUT.slp
"""
import ast
import re
import sys
from fractions import Fraction as Fr


def parse(text):
    """-> list of (name, expression-string); comments (#...) and blank lines skipped."""
    out = []
    body = "\n".join(ln.split("#", 1)[0] for ln in text.splitlines())
    for stmt in body.split(";"):
        stmt = stmt.strip()
        if not stmt:
            continue
        lhs, rhs = stmt.split(":=", 1)
        out.append((lhs.strip(), rhs.strip()))
    return out


def linear(expr, env):
    """exact value of a linear expression as {input: coefficient}; also returns
    (adds, scalings, negations) in the syntactic model used by both tools:
    binary +/- = 1 add, multiply/divide by a constant of modulus != 1 = 1
    scaling, unary minus or multiply by -1 = 1 negation (free in PLinOpt).
    A chain of constant factors on one signal (x*7/16) is ONE scaling by the
    combined constant, as PLinOpt's SLPchecker counts it."""
    counts = [0, 0, 0]

    def ev(node):
        if isinstance(node, ast.Name):
            if node.id not in env:
                raise ValueError(f"undefined {node.id}")
            return dict(env[node.id]), None, None
        if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
            return None, Fr(node.value), None
        if isinstance(node, ast.UnaryOp):
            v, c, _ = ev(node.operand)
            if isinstance(node.op, ast.UAdd):
                return v, c, None
            if c is not None:
                return None, -c, None
            counts[2] += 1
            return {k: -x for k, x in v.items()}, None, None
        if isinstance(node, ast.BinOp):
            lv, lc, lf = ev(node.left)
            rv, rc, rf = ev(node.right)
            if isinstance(node.op, (ast.Add, ast.Sub)):
                if lv is None or rv is None:
                    raise ValueError("affine term")
                sg = 1 if isinstance(node.op, ast.Add) else -1
                # a + (-b) is one subtraction: undo the negation charged for -b
                if isinstance(node.right, ast.UnaryOp) and isinstance(node.right.op, ast.USub):
                    counts[2] -= 1
                counts[0] += 1
                out = dict(lv)
                for k, x in rv.items():
                    out[k] = out.get(k, Fr(0)) + sg * x
                return {k: x for k, x in out.items() if x}, None, None
            if isinstance(node.op, ast.Mult):
                if lc is not None and rc is not None:
                    return None, lc * rc, None
                v, c, f = (lv, rc, lf) if lv is not None else (rv, lc, rf)
            elif isinstance(node.op, ast.Div):
                if lc is not None and rc is not None:
                    return None, lc / rc, None
                if lv is None:
                    raise ValueError("constant / signal")
                v, c, f = lv, 1 / rc, lf
            else:
                raise ValueError("operator")
            if c is None or v is None:
                raise ValueError("nonlinear")
            # fold into the scaling already applied to this signal, if any
            prev = f if f is not None else Fr(1)
            comb = prev * c
            counts[1] += int(abs(comb) != 1) - int(abs(prev) != 1)
            counts[2] += int(comb < 0) - int(prev < 0)
            return {k: c * x for k, x in v.items() if c * x}, None, comb
        raise ValueError(f"unsupported node {ast.dump(node)}")

    v, c, _ = ev(ast.parse(expr, mode="eval").body)
    if v is None:
        raise ValueError(f"scalar expression {expr}")
    return v, counts


def evaluate(prog, n_in):
    """-> (outputs {j: vector dict}, adds, scalings, negations)."""
    env = {f"i{k}": {k: Fr(1)} for k in range(n_in)}
    tot = [0, 0, 0]
    for lhs, rhs in prog:
        v, c = linear(rhs, env)
        env[lhs] = v
        for i in range(3):
            tot[i] += c[i]
    outs = {int(k[1:]): v for k, v in env.items() if re.fullmatch(r"o\d+", k)}
    return outs, tot


def dense(outs, n_in):
    m = max(outs) + 1
    assert set(outs) == set(range(m)), "outputs not contiguous"
    return [[outs[j].get(i, Fr(0)) for i in range(n_in)] for j in range(m)]


def brent(L, R, P):
    """all 4096 equations: sum_k P[c][k] L[k][a] R[k][b] = [A_a B_b contributes to C_c]."""
    r = len(L)
    bad = 0
    for c in range(16):
        got = {}
        for k in range(r):
            w = P[c][k]
            if not w:
                continue
            for a in range(16):
                if not L[k][a]:
                    continue
                for b in range(16):
                    if R[k][b]:
                        got[a, b] = got.get((a, b), Fr(0)) + w * L[k][a] * R[k][b]
        for a in range(16):
            for b in range(16):
                want = 1 if (a // 4 == c // 4 and a % 4 == b // 4 and b % 4 == c % 4) else 0
                if got.get((a, b), Fr(0)) != want:
                    bad += 1
    return bad


def fmt_plinopt(lhs, rhs, env):
    """re-emit one line in SLPchecker syntax when it is a scaling by a
    parenthesized or negative constant; other lines pass through."""
    v, _ = linear(rhs, env)
    m = re.fullmatch(r"\s*(-?)\s*([A-Za-z_]\w*)\s*\*\s*\(?\s*(-?\d+)(?:\s*/\s*(\d+))?\s*\)?\s*", rhs)
    if m:
        neg, name, p, q = m.group(1), m.group(2), int(m.group(3)), int(m.group(4) or 1)
        c = Fr(p, q) * (-1 if neg else 1)
        s = "-" if c < 0 else ""
        c = abs(c)
        if c == 1:
            return f"{lhs}:={s}{name};"
        if c.denominator == 1:
            return f"{lhs}:={s}{name}*{c.numerator};"
        if c.numerator == 1:
            return f"{lhs}:={s}{name}/{c.denominator};"
        return f"{lhs}:={s}{name}*{c.numerator}/{c.denominator};"
    return f"{lhs}:={rhs};"


def emit_plinopt(prog, n_in):
    env = {f"i{k}": {k: Fr(1)} for k in range(n_in)}
    lines = []
    for lhs, rhs in prog:
        lines.append(fmt_plinopt(lhs, rhs, env))
        env[lhs], _ = linear(rhs, env)
    return lines


def main():
    args = sys.argv[1:]
    if args and args[0] == "--emit-plinopt":
        prog = parse(open(args[1]).read())
        n_in = 1 + max(int(m) for _, rhs in prog for m in re.findall(r"\bi(\d+)\b", rhs))
        out = emit_plinopt(prog, n_in)
        open(args[2], "w").write("\n".join(out) + "\n")
        # the translation must compute the same map
        o1, _ = evaluate(prog, n_in)
        o2, _ = evaluate(parse("\n".join(out)), n_in)
        assert o1 == o2, "translation changed the map"
        print(f"wrote {args[2]} ({len(out)} lines, map unchanged)")
        return
    if args and args[0] == "--dir":
        paths = [f"{args[1]}/{p}.slp" for p in "LRP"]
    else:
        paths = [f"{args[0]}_{p}.slp" for p in "LRP"]
    progs = [parse(open(p).read()) for p in paths]
    oL, cL = evaluate(progs[0], 16)
    oR, cR = evaluate(progs[1], 16)
    L, R = dense(oL, 16), dense(oR, 16)
    r = len(L)
    assert len(R) == r, "L and R rank differ"
    oP, cP = evaluate(progs[2], r)
    P = dense(oP, r)
    assert len(P) == 16, "P must have 16 outputs"
    bad = brent(L, R, P)
    pl = [c[0] + c[1] for c in (cL, cR, cP)]
    pt = [sum(c) for c in (cL, cR, cP)]
    for name, c in zip("LRP", (cL, cR, cP)):
        print(f"{name}: adds {c[0]}, scalings {c[1]}, negations {c[2]} -> PLinOpt {c[0] + c[1]}, Patel {sum(c)}")
    print(f"rank {r}; Brent equations failing: {bad} / 4096")
    print(f"TOTAL PLinOpt model (adds + scalings): {sum(pl)}   Patel model (+ negations): {sum(pt)}")
    sys.exit(0 if bad == 0 else 1)


if __name__ == "__main__":
    main()
