#!/usr/bin/env python3
"""windows.py — exact window resynthesis orchestrator (task #31).

Extracts every closed sub-DAG window from a PLinOpt SLP (contiguous
topological op ranges with bounded ops/inputs/outputs), expresses the
window's output wires in the window-input basis over Q, scales to
integers, and emits solver instances for exactw. Modes:

  extract SIDE.slp OUTDIR [maxops] [maxin]   -> instance files + meta
  splice  SIDE.slp OUTDIR/instNNN.sol        -> resynthesized SLP on
                                                stdout (checker gates)

Instance format (exactw input):
  m r budget
  r lines of m integers (targets in input basis, window-scaled)
Cost accounting matches SLPchecker: one add per binary line, one
cmult per non-unit coefficient, one cmult per scaled output match.
"""
import re
import sys
from fractions import Fraction

LINE = re.compile(r"^\s*(\w+)\s*:=\s*(.+?);\s*$")
TERM = re.compile(r"([+-]?)(\w+)((?:[*/]\d+)*)")


def parse(path):
    """ops: list of (name, [(coef Fraction, src)]) in file order."""
    ops = []
    for ln in open(path):
        m = LINE.match(ln)
        if not m:
            continue
        name, expr = m.group(1), m.group(2).replace(" ", "")
        terms = []
        for sign, src, scales in TERM.findall(expr):
            if not src:
                continue
            f = Fraction(-1 if sign == "-" else 1)
            for op, val in re.findall(r"([*/])(\d+)", scales):
                f = f * int(val) if op == "*" else f / int(val)
            terms.append((f, src))
        ops.append((name, terms))
    return ops


def op_cost(terms):
    adds = max(0, len(terms) - 1)
    cmuls = sum(1 for (f, _) in terms if abs(f) != 1)
    return adds + cmuls


def extract(path, outdir, maxops=12, maxin=8, maxout=5):
    import os

    os.makedirs(outdir, exist_ok=True)
    ops = parse(path)
    n = len(ops)
    defined_at = {name: i for i, (name, _) in enumerate(ops)}
    used_after = [set() for _ in range(n + 1)]  # names used at >= i
    use = {}
    for i, (_, terms) in enumerate(ops):
        for _, src in terms:
            use.setdefault(src, []).append(i)
    outputs = {name for (name, _) in ops if name.startswith("o")}

    count = 0
    meta = []
    for i in range(n):
        for j in range(i, min(n, i + maxops)):
            win = ops[i : j + 1]
            win_names = {name for (name, _) in win}
            # inputs: sources referenced by the window, defined outside
            ins = []
            for _, terms in win:
                for _, src in terms:
                    if src not in win_names and src not in ins:
                        ins.append(src)
            if len(ins) > maxin:
                break  # widening j only adds inputs
            # outputs: window wires used after j, or program outputs
            outs = [
                name
                for (name, _) in win
                if name in outputs
                or any(k > j for k in use.get(name, []))
            ]
            if not (0 < len(outs) <= maxout):
                continue
            cost = sum(op_cost(t) for (_, t) in win)
            if cost < 2:
                continue  # nothing to save
            # window wires in input basis over Q
            basis = {nm: [Fraction(int(nm == x)) for x in ins] for nm in ins}
            ok = True
            for name, terms in win:
                v = [Fraction(0)] * len(ins)
                for f, src in terms:
                    sv = basis.get(src)
                    if sv is None:
                        ok = False
                        break
                    v = [a + f * b for a, b in zip(v, sv)]
                if not ok:
                    break
                basis[name] = v
            if not ok:
                continue
            tgts = [basis[o] for o in outs]
            # scale to integers (window-local power of 2)
            denlcm = 1
            for t in tgts:
                for x in t:
                    denlcm = max(denlcm, x.denominator)
            scale = denlcm  # denominators are powers of 2 here
            itgts = [[int(x * scale) for x in t] for t in tgts]
            inst = f"{outdir}/inst{count:04d}.txt"
            with open(inst, "w") as f:
                f.write(f"{len(ins)} {len(tgts)} {cost - 1} {scale}\n")
                for t in itgts:
                    f.write(" ".join(map(str, t)) + "\n")
            meta.append(
                f"inst{count:04d} range {i} {j} cost {cost} scale {scale} "
                f"ins {' '.join(ins)} outs {' '.join(outs)}"
            )
            count += 1
    with open(f"{outdir}/meta.txt", "w") as f:
        f.write("\n".join(meta) + "\n")
    print(f"{count} instances -> {outdir}")


def splice(path, solpath):
    """Splice a solver solution back into the full SLP; print it."""
    import os

    outdir = os.path.dirname(solpath)
    instname = os.path.basename(solpath).replace(".sol", "")
    meta = None
    for ln in open(f"{outdir}/meta.txt"):
        if ln.startswith(instname + " "):
            meta = ln.split()
            break
    assert meta, "instance not in meta"
    i, j = int(meta[2]), int(meta[3])
    scale = int(meta[6])
    ins = meta[meta.index("ins") + 1 : meta.index("outs")]
    outs = meta[meta.index("outs") + 1 :]
    ops = parse(path)

    # solution: lines "a i b j" meaning w = a*w_i + b*w_j over the
    # INTEGER window space; wires 0..m-1 are inputs; then new wires.
    # final r lines: "match t wire e" meaning target t = 2^e * wire.
    sol_ops = []
    matches = []
    for ln in open(solpath):
        f = ln.split()
        if not f:
            continue
        if f[0] == "match":
            matches.append((int(f[1]), int(f[2]), int(f[3]), int(f[4])))
        else:
            sol_ops.append((int(f[0]), int(f[1]), int(f[2]), int(f[3])))

    def coefstr(c, name, lead):
        sgn = "-" if c < 0 else ("" if lead else "+")
        mag = abs(c)
        return f"{sgn}{name}" + ("" if mag == 1 else f"*{mag}")

    new_lines = []
    wnames = list(ins)
    for k, (a, wi, b, wj) in enumerate(sol_ops):
        nm = f"xw{k}"
        expr = coefstr(a, wnames[wi], True) + coefstr(b, wnames[wj], False)
        new_lines.append(f"{nm}:={expr};")
        wnames.append(nm)
    # outputs: target t = 2^e * wire  =>  out = wire * 2^-e / scale ...
    # in window space targets are scale * (true value); true out =
    # (2^e * wire) / scale with e from the match line.
    for t, w, e, sgn in matches:
        nm = outs[t]
        num = 2**e if e >= 0 else 1
        den = (2**-e if e < 0 else 1) * scale
        # reduce
        from math import gcd

        g = gcd(num, den)
        num //= g
        den //= g
        expr = ("-" if sgn < 0 else "") + wnames[w]
        if num != 1:
            expr += f"*{num}"
        if den != 1:
            expr += f"/{den}"
        new_lines.append(f"{nm}:={expr};")

    for k, (name, terms) in enumerate(ops):
        if i <= k <= j:
            if k == i:
                for nl in new_lines:
                    print(nl)
            continue
        parts = []
        for f, src in terms:
            sgn = "-" if f < 0 else ("" if not parts else "+")
            mag = abs(f)
            piece = f"{sgn}{src}"
            if mag.numerator != 1:
                piece += f"*{mag.numerator}"
            if mag.denominator != 1:
                piece += f"/{mag.denominator}"
            parts.append(piece)
        print(f"{name}:={''.join(parts)};")


if __name__ == "__main__":
    if sys.argv[1] == "extract":
        extract(sys.argv[2], sys.argv[3], *map(int, sys.argv[4:]))
    elif sys.argv[1] == "splice":
        splice(sys.argv[2], sys.argv[3])
