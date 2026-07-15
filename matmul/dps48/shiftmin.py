#!/usr/bin/env python3
"""shiftmin v2 — shift-slack hunt on a fixed additive skeleton, with
a real expression parser (inline parenthesized groups become virtual
nodes). Relabel wires by exponents (inputs/outputs pinned 0); cost =
#(scaled terms) + #(divided lines/groups); coordinate descent +
restarts; emits their syntax; SLPchecker referees.
Usage: shiftmin.py in.slp out.slp [restarts]
"""
import random
import re
import sys

LINE = re.compile(r"^\s*(\w+)\s*:=\s*(.+?);\s*$")
POW = {"2": 1, "4": 2, "8": 3, "16": 4}


def parse(path):
    ops = []
    vcount = [0]

    def parse_expr(s):
        terms = []
        i = 0
        sign = 1
        n = len(s)
        while i < n:
            c = s[i]
            if c == "+":
                sign = 1
                i += 1
                continue
            if c == "-":
                sign = -1
                i += 1
                continue
            if c == "(":
                depth = 1
                j = i + 1
                while j < n and depth:
                    depth += s[j] == "("
                    depth -= s[j] == ")"
                    j += 1
                inner = s[i + 1 : j - 1]
                k = 0
                while j < n and s[j] in "*/":
                    mm = re.match(r"([*/])(\d+)", s[j:])
                    k += POW[mm.group(2)] * (1 if mm.group(1) == "*" else -1)
                    j += mm.end()
                vname = f"v{vcount[0]}"
                vcount[0] += 1
                vterms = parse_expr(inner)
                ops.append((vname, vterms))
                terms.append((sign, vname, k))
                sign = 1
                i = j
                continue
            m = re.match(r"(\w+)", s[i:])
            src = m.group(1)
            i += m.end()
            k = 0
            while i < n and s[i] in "*/":
                mm = re.match(r"([*/])(\d+)", s[i:])
                k += POW[mm.group(2)] * (1 if mm.group(1) == "*" else -1)
                i += mm.end()
            terms.append((sign, src, k))
            sign = 1
        return terms

    for ln in open(path):
        m = LINE.match(ln)
        if not m:
            continue
        name, expr = m.groups()
        terms = parse_expr(expr.replace(" ", ""))
        ops.append((name, terms))
    return ops


def line_cost(terms, e, ew):
    exps = [ew - e.get(src, 0) + k for (_, src, k) in terms]
    lo = max(0, -min(exps)) if exps else 0
    best = None
    for dp in range(lo, lo + 3):
        gs = [x + dp for x in exps]
        c = sum(1 for g in gs if g > 0) + (1 if dp > 0 else 0)
        if best is None or c < best:
            best = c
    return 99 if best is None else best


def cost_of(ops, e):
    return sum(line_cost(t, e, e.get(n, 0)) for (n, t) in ops)


def emit(ops, e, path):
    out = []
    for name, terms in ops:
        ew = e.get(name, 0)
        exps = [ew - e.get(src, 0) + k for (_, src, k) in terms]
        lo = max(0, -min(exps)) if exps else 0
        bestdp, bestc = lo, None
        for dp in range(lo, lo + 3):
            gs = [x + dp for x in exps]
            c = sum(1 for g in gs if g > 0) + (1 if dp > 0 else 0)
            if bestc is None or c < bestc:
                bestc, bestdp = c, dp
        parts = []
        for (s, src, _), x in zip(terms, exps):
            g = x + bestdp
            t = src + (f"*{2**g}" if g > 0 else "")
            parts.append(("-" if s < 0 else ("+" if parts else "")) + t)
        body = "".join(parts)
        if bestdp > 0:
            out.append(f"{name}:=({body})/{2**bestdp};")
        else:
            out.append(f"{name}:={body};")
    open(path, "w").write("\n".join(out) + "\n")


def main():
    inp, outp = sys.argv[1], sys.argv[2]
    restarts = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    ops = parse(inp)
    internal = [n for (n, _) in ops if not n.startswith("o")]
    rng = random.Random(11)
    base_cost = cost_of(ops, {})
    best_e, best_c = {}, base_cost
    for r in range(restarts):
        e = {} if r == 0 else {n: rng.choice([-1, 0, 0, 1]) for n in internal}
        for _ in range(50):
            improved = False
            for n in internal:
                cur = e.get(n, 0)
                cbest, ebest = None, cur
                for v in range(-3, 4):
                    e[n] = v
                    c = cost_of(ops, e)
                    if cbest is None or c < cbest:
                        cbest, ebest = c, v
                e[n] = ebest
                improved |= ebest != cur
            if not improved:
                break
        c = cost_of(ops, e)
        if c < best_c:
            best_c, best_e = c, dict(e)
            print(f"[restart {r}] cost {base_cost} -> {c}")
    print(f"shiftmin: original scale-cost {base_cost}, best {best_c}")
    emit(ops, best_e, outp)


if __name__ == "__main__":
    main()
