#!/usr/bin/env python3
"""Generate fused streaming kernels for fast matrix multiplication schemes (practical track).

A scheme <n0 x n0 x n0 : r> splits A, B, C into n0 x n0 grids of blocks and is three linear
programs (straight-line programs in PLinOpt's .slp format): L maps the n0^2 blocks of A to the r
left factors S_k, R maps the blocks of B to the right factors T_k, and P maps the r products
M_k = S_k T_k to the blocks of C (our convention vec(AB) = P((L vecA) . (R vecB)), row-major).
The same linear map acts on every element position of the blocks, so each program is emitted
as one loop over element positions whose body is the whole program on scalars: one pass over
memory reads every input block once and writes every output block once, intermediates stay in
registers, and the program's operation count costs only arithmetic.  Also emitted, for the
op-by-op comparison: the program as a list of block operations (one pass per operation).

Schemes: sw (Strassen-Winograd <2x2x2:7>, 15 additions), sw2 (its Kronecker square, one
<4x4x4:49> scheme, 165 additions), dps48 (our <4x4x4:48> at 201 operations, from
../dps48/cand48/p005_201n_{L,R,P}.slp).

  gen_kernels.py OUT.h [--fma]
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CAND = os.path.join(HERE, "..", "dps48", "cand48")

# Strassen-Winograd in PLinOpt's format.  Blocks row-major: A0 = A11, A1 = A12, A2 = A21, A3 = A22.
# S1 = A21 + A22, S2 = S1 - A11, S3 = A11 - A21, S4 = A12 - S2; products M1..M7 =
# A11 B11, A12 B21, S4 B22, A22 T4, S1 T1, S2 T2, S3 T3.
SW_L = """t1:=i2+i3;
t2:=t1-i0;
t3:=i0-i2;
t4:=i1-t2;
o0:=i0;
o1:=i1;
o2:=t4;
o3:=i3;
o4:=t1;
o5:=t2;
o6:=t3;
"""
# T1 = B12 - B11, T2 = B22 - T1, T3 = B22 - B12, T4 = T2 - B21
SW_R = """t1:=i1-i0;
t2:=i3-t1;
t3:=i3-i1;
t4:=t2-i2;
o0:=i0;
o1:=i2;
o2:=i3;
o3:=t4;
o4:=t1;
o5:=t2;
o6:=t3;
"""
# U1 = M1 + M2 (C11), U2 = M1 + M6, U3 = U2 + M7, U4 = U2 + M5, U5 = U4 + M3 (C12),
# U6 = U3 - M4 (C21), U7 = U3 + M5 (C22)
SW_P = """t1:=i0+i1;
t2:=i0+i5;
t3:=t2+i6;
t4:=t2+i4;
t5:=t4+i2;
t6:=t3-i3;
t7:=t3+i4;
o0:=t1;
o1:=t5;
o2:=t6;
o3:=t7;
"""

LINE = re.compile(r"^(\w+):=(-?)(\w+)(?:([-+*/])(\w+))?;$")


def parse(text):
    """-> (n_inputs, n_outputs, ops) with ops (lhs, neg, a, op, b) in order"""
    ops, ni, no = [], 0, 0
    for ln in text.splitlines():
        ln = ln.strip()
        if not ln or ln.startswith("#"):
            continue
        m = LINE.match(ln)
        assert m, f"unparsed line: {ln}"
        lhs, neg, a, op, b = m.groups()
        ops.append((lhs, neg == "-", a, op, b))
        for v in (a, b):
            if v and v.startswith("i"):
                ni = max(ni, int(v[1:]) + 1)
        if lhs.startswith("o"):
            no = max(no, int(lhs[1:]) + 1)
    return ni, no, ops


def kron(text1, text2, outer_first):
    """the program of A -> (P1 (x) P2) A for block grids: inputs indexed (outer, inner),
    outer_first: apply program 1 along the outer index first (L, R) or program 2 along the inner
    index first (P); returns PLinOpt text with inputs/outputs in the 4x4 row-major order"""
    n1, m1, ops1 = parse(text1)
    n2, m2, ops2 = parse(text2)
    assert n1 == n2 and m1 == m2
    lines, cnt = [], [0]

    def emit(ops, inputs):
        """inline a program on named inputs; returns its output names"""
        env, outs = {f"i{k}": v for k, v in enumerate(inputs)}, {}
        for lhs, neg, a, op, b in ops:
            av = env[a] if not a[0].isdigit() else a
            if lhs.startswith("o"):
                assert op is None and not neg, "output lines are plain copies here"
                outs[int(lhs[1:])] = av
                continue
            cnt[0] += 1
            name = f"k{cnt[0]}"
            rhs = ("-" if neg else "") + av + ((op + (env[b] if not b[0].isdigit() else b)) if op else "")
            lines.append(f"{name}:={rhs};")
            env[lhs] = name
        return [outs[k] for k in range(len(outs))]

    # 2x2 grids of 2x2 grids: outer index o = 2 ro + co, inner i = 2 ri + ci, row-major 4x4
    # position (2 ro + ri, 2 co + ci)
    def pos(o, i):
        ro, co, ri, ci = o // 2, o % 2, i // 2, i % 2
        return 4 * (2 * ro + ri) + (2 * co + ci)

    if outer_first:   # L, R: 16 inputs -> 49 outputs indexed 7 k_out + k_in
        stage1 = [emit(ops1, [f"i{pos(o, i)}" for o in range(4)]) for i in range(4)]  # [i][k_out]
        outs = []
        for ko in range(m1):
            outs += emit(ops2, [stage1[i][ko] for i in range(4)])                     # k_in
        return "\n".join(lines + [f"o{k}:={v};" for k, v in enumerate(outs)]) + "\n"
    # P: 49 inputs (7 k_out + k_in) -> 16 outputs; here the rank is the input count
    rank = n1
    stage1 = [emit(ops2, [f"i{rank * ko + ki}" for ki in range(rank)]) for ko in range(rank)]  # [k_out][i]
    res = {}
    for i in range(4):
        outs = emit(ops1, [stage1[ko][i] for ko in range(rank)])                          # [o]
        for o in range(4):
            res[pos(o, i)] = outs[o]
    return "\n".join(lines + [f"o{k}:={res[k]};" for k in range(16)]) + "\n"


def c_expr(neg, a, op, b, T):
    va = a if a.startswith(("i", "t", "k")) else f"(({T}){a})"
    if a.startswith("i"):
        va = f"{a}[c]"
    if op is None:
        return ("-" if neg else "") + va
    vb = f"{b}[c]" if b.startswith("i") else (b if b.startswith(("t", "k")) else f"(({T}){b})")
    if op in "*/" and not b.startswith(("i", "t", "k")):
        vb = f"(({T}){b})"
    return f"{'-' if neg else ''}{va} {op} {vb}"


def fused(name, text, T, in_ld, out_ld, fma=False):
    """one streaming loop: rows r0..r1 of every block, the program per element position; with
    fma, every addition that uses a scaled value x * s computes fma(x, s, other) instead (one
    fused multiply-add; exact for s a power of two, so the results are unchanged)"""
    ni, no, ops = parse(text)
    scaled = {}
    for lhs, neg, a, op, b in ops:
        if op in ("*", "/") and b and b[0].isdigit() and not neg:
            scaled[lhs] = (a, f"(({T}){b})" if op == "*" else f"(({T})1 / ({T}){b})")
    s = [f"static void {name}(size_t m, size_t ld_in, size_t ld_out, const {T} *const *in, "
         f"{T} *const *out, size_t r0, size_t r1) {{",
         "    for (size_t r = r0; r < r1; r++) {"]
    s += [f"        const {T} *restrict i{k} = in[{k}] + r * ld_in;" for k in range(ni)]
    s += [f"        {T} *restrict o{k} = out[{k}] + r * ld_out;" for k in range(no)]
    # the element positions are independent (every output block is distinct from every input
    # block); with 64 streams the vectorizer would otherwise give up on its overlap checks
    s.append("        _Pragma(\"clang loop vectorize(assume_safety) interleave(enable)\")")
    s.append("        for (size_t c = 0; c < m; c++) {")
    fn = "fmaf" if T == "float" else "fma"
    ref = lambda v: f"{v}[c]" if v.startswith("i") else v
    for lhs, neg, a, op, b in ops:
        e = c_expr(neg, a, op, b, T)
        if fma and op in ("+", "-") and not neg and (a in scaled or b in scaled):
            if a in scaled:                         # x*s + b, x*s - b
                x, f = scaled[a]
                e = f"{fn}({ref(x)}, {f}, {'' if op == '+' else '-'}{ref(b)})"
            else:                                   # a + x*s, a - x*s
                x, f = scaled[b]
                e = f"{fn}({ref(x)}, {'' if op == '+' else '-'}{f}, {ref(a)})"
        if lhs.startswith("o"):
            s.append(f"            {lhs}[c] = {e};")
        else:
            s.append(f"            const {T} {lhs} = {e};")
    s += ["        }", "    }", "}", ""]
    return "\n".join(s)


def opbyop(name, text):
    """the program as block operations: (dst, kind, a, b) with kinds copy/add/sub/scale"""
    ni, no, ops = parse(text)
    rows = []
    for lhs, neg, a, op, b in ops:
        assert not neg
        kind = {None: 0, "+": 1, "-": 2, "*": 3, "/": 4}[op]
        def ref(v):
            if v is None:
                return -1
            if v[0].isdigit():
                return int(v)
            return {"i": 0, "t": 100000, "o": 200000, "k": 300000}[v[0]] + int(v[1:])
        rows.append(f"{{{ref(lhs)}, {kind}, {ref(a)}, {ref(b)}}}")
    return f"static const int {name}[][4] = {{\n    " + ",\n    ".join(rows) + "\n};\n" \
           f"static const int {name}_len = {len(rows)};\n"


def main():
    out = sys.argv[1]
    fma = "--fma" in sys.argv
    schemes = {
        "sw": (SW_L, SW_R, SW_P),
        "sw2": (kron(SW_L, SW_L, True), kron(SW_R, SW_R, True), kron(SW_P, SW_P, False)),
        "dps48": tuple(open(os.path.join(CAND, f"p005_201n_{s}.slp")).read() for s in "LRP"),
    }
    h = ["/* generated by gen_kernels.py: fused streaming kernels per scheme"
         + (" (scalings folded into fused multiply-adds)" if fma else "") + " */",
         "#include <math.h>", "#include <stddef.h>", ""]
    for name, (l, r, p) in schemes.items():
        (nl, rk, _), (_, _, _), (_, nc, _) = parse(l), parse(r), parse(p)
        nops = sum(1 for t in (l, r, p) for o in parse(t)[2] if o[3] is not None or o[1])
        h.append(f"/* {name}: {nl} blocks -> {rk} products -> {nc} blocks, {nops} operations */")
        h.append(f"enum {{ {name.upper()}_NB = {nl}, {name.upper()}_RANK = {rk}, {name.upper()}_OPS = {nops} }};")
        for T, suf in (("float", "f"), ("double", "d")):
            h.append(fused(f"{name}_L_{suf}", l, T, 0, 0, fma))
            h.append(fused(f"{name}_R_{suf}", r, T, 0, 0, fma))
            h.append(fused(f"{name}_P_{suf}", p, T, 0, 0, fma))
        for side, t in (("L", l), ("R", r), ("P", p)):
            h.append(opbyop(f"{name}_{side}_ops", t))
        print(f"{name}: {nl} blocks, rank {rk}, {nops} operations "
              f"(L {sum(1 for o in parse(l)[2] if o[3])}, R {sum(1 for o in parse(r)[2] if o[3])}, "
              f"P {sum(1 for o in parse(p)[2] if o[3])})")
    open(out, "w").write("\n".join(h))


if __name__ == "__main__":
    main()
