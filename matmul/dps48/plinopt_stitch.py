#!/usr/bin/env python3
"""Stitch three PLinOpt SLPs (side L, side R, output P of one of our
gauged slot-variant instances) into a complete 4x4x4:48 algorithm and
prove it independently: exact Fractions, ALL 256 basis pairs, random
trials, and a from-scratch op recount.

PLinOpt syntax handled: `w:=expr;`, `w+=expr;`, `w-=expr;` where expr
is a signed sum of terms, each `[coef*]var` with rational coef.

Usage: plinopt_stitch.py L.slp R.slp P.slp
"""
import re
import sys
from fractions import Fraction


TOK = re.compile(r"\d+|[A-Za-z_]\w*|[()+\-*/]")


class Expr:
    """recursive-descent parser for PLinOpt right-hand sides:
    sums of products/quotients of (numbers | vars | parenthesized)."""

    def __init__(self, text):
        self.t = TOK.findall(text)
        self.i = 0
        self.adds = 0
        self.mults = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self):
        x = self.t[self.i]
        self.i += 1
        return x

    def parse(self, env):
        v = self.sum(env)
        assert self.peek() is None, self.t[self.i:]
        return v

    def sum(self, env):
        neg = False
        if self.peek() in ("+", "-"):
            neg = self.eat() == "-"
        v = self.prod(env)
        if neg:
            v = -v          # unary negation: free
        while self.peek() in ("+", "-"):
            op = self.eat()
            w = self.prod(env)
            self.adds += 1
            v = v - w if op == "-" else v + w
        return v

    def prod(self, env):
        v, isconst = self.atom(env)
        while self.peek() in ("*", "/"):
            op = self.eat()
            w, wconst = self.atom(env)
            if op == "*":
                # coefficient mult counts unless it is +-1
                if (isconst and abs(v) != 1) or (wconst and abs(w) != 1) \
                        or not (isconst or wconst):
                    self.mults += 1
                v = v * w
            else:
                if not (wconst and abs(w) == 1):
                    self.mults += 1
                v = v / w
            isconst = isconst and wconst
        return v

    def atom(self, env):
        tk = self.eat()
        if tk == "(":
            v = self.sum(env)
            assert self.eat() == ")"
            return v, False
        if tk.isdigit():
            return Fraction(tk), True
        return env[tk], False


def parse_slp(path):
    """statements as (target, op, rhs-text); returns (stmts, adds,
    mults) with ops counted by one dry-run parse over a dummy env."""
    stmts = []
    txt = open(path).read()
    for stmt in txt.split(";"):
        stmt = stmt.strip()
        if not stmt or stmt.startswith("#"):
            continue
        m = re.match(r"^(\w+)\s*(:=|\+=|-=)\s*(.+)$", stmt, re.S)
        assert m, stmt
        stmts.append((m.group(1), m.group(2),
                      m.group(3).replace("\n", " ")))
    # dry run for counting with a defaultdict-ish env of zeros
    class Z(dict):
        def __missing__(self, k):
            return Fraction(0)
    adds = mults = 0
    env = Z()
    for w, op, rhs in stmts:
        e = Expr(rhs)
        v = e.parse(env)
        adds += e.adds
        mults += e.mults
        if op == "+=":
            adds += 1
            env[w] = env[w] + v
        elif op == "-=":
            adds += 1
            env[w] = env[w] - v
        else:
            env[w] = v
    return stmts, adds, mults


def run(prog, env):
    for w, op, rhs in prog:
        v = Expr(rhs).parse(env)
        if op == ":=":
            env[w] = v
        elif op == "+=":
            env[w] = env.get(w, Fraction(0)) + v
        else:
            env[w] = env.get(w, Fraction(0)) - v
    return env


def apply_map(prog, invals, nin, nout):
    env = {f"i{k}": Fraction(invals[k]) for k in range(nin)}
    env = run(prog, env)
    return [env[f"o{z}"] for z in range(nout)]


def matmul4(a, b):
    return [sum(a[4 * i + k] * b[4 * k + j] for k in range(4))
            for i in range(4) for j in range(4)]


def main():
    lp, la, lm = parse_slp(sys.argv[1])
    rp, ra, rm = parse_slp(sys.argv[2])
    pp, pa, pm = parse_slp(sys.argv[3])
    print(f"L: {la} adds + {lm} mults | R: {ra}+{rm} | P: {pa}+{pm}")
    total = la + lm + ra + rm + pa + pm
    print(f"TOTAL: {total} ops (+48 products)")

    def algo(av, bv):
        f1 = apply_map(lp, av, 16, 48)
        f2 = apply_map(rp, bv, 16, 48)
        prods = [f1[i] * f2[i] for i in range(48)]
        return apply_map(pp, prods, 48, 16)

    for x in range(16):
        for y in range(16):
            av = [1 if i == x else 0 for i in range(16)]
            bv = [1 if i == y else 0 for i in range(16)]
            assert algo(av, bv) == matmul4(av, bv), f"basis ({x},{y})"
    print("basis pairs : PASS (256/256 — complete bilinear proof)")

    import random
    rng = random.Random(7)
    for _ in range(100):
        av = [rng.randint(-50, 50) for _ in range(16)]
        bv = [rng.randint(-50, 50) for _ in range(16)]
        assert algo(av, bv) == matmul4(av, bv)
    print("random      : PASS (100)")
    print(f"VERDICT     : VERIFIED {total}-op rational <4x4x4:48> algorithm")


if __name__ == "__main__":
    main()
