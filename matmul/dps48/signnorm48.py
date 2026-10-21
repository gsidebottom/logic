#!/usr/bin/env python3
"""Sign normalization of an L/R/P program triple: re-emit every program so
that no binary operation negates both operands, no scaling is negative, and
output negations of L and R are absorbed into the signs of P's inputs (the
products), so that Patel's cost model (which charges negations) agrees with
PLinOpt's (which does not) up to the output negations of P that remain
forced.  The maps are unchanged: L_k, R_k may flip sign together with P's
column k; the triple is re-checked exactly.

Usage: signnorm48.py IN_PREFIX OUT_PREFIX     (PREFIX_{L,R,P}.slp)
"""
import ast
import re
import sys
from fractions import Fraction as Fr

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import slp48check as C  # noqa: E402


class Node:
    __slots__ = ("kind", "u", "v", "a", "b", "c", "vec", "name", "sign")

    def __init__(self, kind, u=None, v=None, a=1, b=1, c=Fr(1), vec=None):
        self.kind, self.u, self.v, self.a, self.b, self.c, self.vec = kind, u, v, a, b, c, vec
        self.name, self.sign = None, 1


def build_dag(prog, n_in):
    """evaluate the program into a DAG of charged nodes; returns (nodes in
    order, env name -> (node, sign), outputs [(k, node, sign)])."""
    inputs = {}
    nodes = []
    for k in range(n_in):
        nd = Node("input", vec={k: Fr(1)})
        nd.name = f"i{k}"
        inputs[k] = nd
    env = {f"i{k}": (inputs[k], 1) for k in range(n_in)}
    by_vec = {}

    def key(vec):
        return tuple(sorted(vec.items()))

    def intern(nd):
        """reuse an existing node computing +-vec"""
        k = key(nd.vec)
        neg = key({i: -x for i, x in nd.vec.items()})
        if k in by_vec:
            return by_vec[k], 1
        if neg in by_vec:
            return by_vec[neg], -1
        by_vec[k] = nd
        nodes.append(nd)
        return nd, 1

    def ev(node):
        # returns (Node or None for constants, sign, const)
        if isinstance(node, ast.Name):
            nd, s = env[node.id]
            return nd, s, None
        if isinstance(node, ast.Constant):
            return None, 1, Fr(node.value)
        if isinstance(node, ast.UnaryOp):
            nd, s, c = ev(node.operand)
            if isinstance(node.op, ast.UAdd):
                return nd, s, c
            return (nd, -s, None) if nd is not None else (None, 1, -c)
        if isinstance(node, ast.BinOp):
            lu, ls, lc = ev(node.left)
            ru, rs, rc = ev(node.right)
            if isinstance(node.op, (ast.Add, ast.Sub)):
                sg = 1 if isinstance(node.op, ast.Add) else -1
                vec = {}
                for i, x in lu.vec.items():
                    vec[i] = vec.get(i, Fr(0)) + ls * x
                for i, x in ru.vec.items():
                    vec[i] = vec.get(i, Fr(0)) + sg * rs * x
                vec = {i: x for i, x in vec.items() if x}
                nd, s = intern(Node("add", u=lu, v=ru, a=ls, b=sg * rs, vec=vec))
                return nd, s, None
            if isinstance(node.op, ast.Mult):
                if lu is None and ru is None:
                    return None, 1, lc * rc
                nd, s, c = (lu, ls, rc) if lu is not None else (ru, rs, lc)
            else:
                if lu is None:
                    return None, 1, lc / rc
                nd, s, c = lu, ls, 1 / rc
            c = c * s
            if abs(c) == 1:
                return nd, 1 if c > 0 else -1, None
            vec = {i: c * x for i, x in nd.vec.items()}
            out, s2 = intern(Node("scale", u=nd, c=c, vec=vec))
            return out, s2, None
        raise ValueError(ast.dump(node))

    outputs = []
    for lhs, rhs in prog:
        nd, s, c = ev(ast.parse(rhs, mode="eval").body)
        assert nd is not None, f"scalar statement {lhs}"
        env[lhs] = (nd, s)
        m = re.fullmatch(r"o(\d+)", lhs)
        if m:
            outputs.append((int(m.group(1)), nd, s))
    outputs.sort(key=lambda t: t[0])
    return nodes, outputs


def emit(nodes, outputs, want=None):
    """sign-aware emission; `want` maps output index -> desired sign of the
    stored output relative to the computed value (default +1).  Returns
    (text, output_signs) where output_signs[k] = sign actually emitted
    relative to the program's original output (+1 = same, -1 = negated)."""
    want = want or {}
    # preferred stored sign for a node that is an output: so that o := node needs no negation
    pref = {}
    for k, nd, s in outputs:
        pref.setdefault(id(nd), s * want.get(k, 1))
    lines = []
    t = 0
    for nd in nodes:
        t += 1
        nd.name = f"t{t}"
        p = pref.get(id(nd), 1)
        if nd.kind == "scale":
            c = nd.c * nd.u.sign  # coefficient relative to the stored operand
            nd.sign = 1 if c > 0 else -1
            c = abs(c)
            if c.denominator == 1:
                rhs = f"{nd.u.name}*{c.numerator}"
            elif c.numerator == 1:
                rhs = f"{nd.u.name}/{c.denominator}"
            else:
                rhs = f"{nd.u.name}*{c.numerator}/{c.denominator}"
        else:
            ca, cb = nd.a * nd.u.sign, nd.b * nd.v.sign
            un, vn = nd.u.name, nd.v.name
            if ca > 0 and cb > 0:
                rhs, nd.sign = f"{un}+{vn}", 1
            elif ca < 0 and cb < 0:
                rhs, nd.sign = f"{un}+{vn}", -1
            elif ca > 0:  # x = u - v
                rhs, nd.sign = (f"{un}-{vn}", 1) if p > 0 else (f"{vn}-{un}", -1)
            else:  # x = v - u
                rhs, nd.sign = (f"{vn}-{un}", 1) if p > 0 else (f"{un}-{vn}", -1)
        lines.append(f"{nd.name}:={rhs};")
    signs = {}
    for k, nd, s in outputs:
        emitted = s * nd.sign * want.get(k, 1)  # +1: o_k := node as stored equals want * value
        signs[k] = want.get(k, 1)
        lines.append(f"o{k}:={'-' if emitted < 0 else ''}{nd.name};")
    return "\n".join(lines) + "\n", signs


def count(text):
    prog = C.parse(text)
    n_in = 1 + max(int(m) for _, rhs in prog for m in re.findall(r"\bi(\d+)\b", rhs))
    _, c = C.evaluate(prog, n_in)
    return c


def main():
    src, dst = sys.argv[1], sys.argv[2]
    progs = {s: C.parse(open(f"{src}_{s}.slp").read()) for s in "LRP"}
    rank = len(C.evaluate(progs["L"], 16)[0])
    # L and R: emit with free choice of output sign (prefer no negation), record the
    # sign each output ends up with relative to the original program
    texts, flips = {}, {}
    for s in "LR":
        nodes, outputs = build_dag(progs[s], 16)
        # choose want so that o_k := node carries no negation: want = s * nd.sign is only
        # known after emission; emit once with want=+1, then flip the outputs that got '-'
        text, _ = emit(nodes, outputs)
        neg = {int(m.group(1)) for m in re.finditer(r"^o(\d+):=-", text, re.M)}
        want = {k: (-1 if k in neg else 1) for k in range(rank)}
        for nd in nodes:
            nd.sign = 1
        text, _ = emit(nodes, outputs, want)
        assert not re.search(r"^o\d+:=-", text, re.M), "L/R output negation remains"
        texts[s] = text
        flips[s] = want  # output k of the new program = want[k] * original output k
    # P: input k (product k) flips by flips[L][k] * flips[R][k]; substitute and re-emit
    nodes, outputs = build_dag(progs["P"], rank)
    for nd in nodes:
        nd.sign = 1
    for k in range(rank):
        f = flips["L"][k] * flips["R"][k]
        if f < 0:
            # the stored input signal is now -i_k: account for it as a stored sign
            pass
    # inputs are nodes too: set their stored sign to the product flip
    input_nodes = {}
    for nd in nodes:
        for op in (nd.u, nd.v):
            if op is not None and op.kind == "input":
                input_nodes[op.name] = op
    for name, nd in input_nodes.items():
        k = int(name[1:])
        nd.sign = flips["L"][k] * flips["R"][k]
    texts["P"], _ = emit(nodes, outputs)
    for s in "LRP":
        open(f"{dst}_{s}.slp", "w").write(texts[s])
    # the matrices of the normalized triple (rows of L, R and columns of P may have
    # flipped sign together), in PLinOpt's sms format, for SLPchecker/MMchecker
    for s in "LRP":
        prog = C.parse(texts[s])
        n_in = rank if s == "P" else 16
        outs, _ = C.evaluate(prog, n_in)
        M = C.dense(outs, n_in)
        with open(f"{dst}_{s}.sms", "w") as f:
            f.write(f"{len(M)} {n_in} R\n")
            for i, row in enumerate(M):
                for j, x in enumerate(row):
                    if x:
                        f.write(f"{i + 1} {j + 1} {x}\n")
            f.write("0 0 0\n")
    for s in "LRP":
        c = count(texts[s])
        print(f"{s}: adds {c[0]}, scalings {c[1]}, negations {c[2]} -> PLinOpt {c[0] + c[1]}, Patel {sum(c)}")
    import subprocess
    r = subprocess.run([sys.executable, C.__file__, dst], capture_output=True, text=True)
    print(r.stdout.strip().splitlines()[-2:])
    sys.exit(r.returncode)


if __name__ == "__main__":
    main()
