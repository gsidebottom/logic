#!/usr/bin/env python3
"""qexact: exact minimum-operation straight-line programs for small linear
maps over Z[1/2], in PLinOpt's cost model (step 3 of the rank-48 campaign).

Model.  Signals are linear forms in the m inputs, held as integer vectors
over a common power-of-two denominator.  The inputs and their negations
are free.  Every produced signal costs one operation: an addition
x = +-a +-b of two available signals, or a scaling x = c a with
c in {+-2, +-1/2, +-4, +-1/4}.  (PLinOpt's x := (a+b)/2 is two
operations: the sum, then its halving.)  The targets are counted up to
sign; a target that is +-an input costs nothing.

Exactness.  Let T be the targets that are not +-inputs.  A program
produces |T| targets plus h helpers (non-target signals), so it costs
|T| + h.  Any target producible in one operation from the available
signals can be produced at once without loss (producing a target only
enlarges the available set), so the waste-free closure of the inputs
decides h = 0, and iterative deepening on h, with each helper a one-op
combination of the signals available when it is introduced, is exact.
Helpers introduced while both are available are taken in increasing
order (bubble-sort argument), and the last helper must put some missing
target one operation away.

API: solve(inputs_m, targets, hmax, node_cap) -> (cost, program) or None,
where program is a list of (name, kind, args) with kind 'add' (a, sa, b,
sb) or 'scale' (a, c); emit_slp renders PLinOpt syntax.  Vectors are
tuples of ints over denominator DEN.
"""
import itertools
import time
from fractions import Fraction as Fr

DEN = 64  # all vectors hold numerators over 1/64
SCALARS = [Fr(2), Fr(1, 2), Fr(4), Fr(1, 4)]


def norm(v):
    """canonical sign: first nonzero coordinate positive; returns (key, sign)."""
    for x in v:
        if x:
            return (tuple(-y for y in v), -1) if x < 0 else (tuple(v), 1)
    return (tuple(v), 1)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def scale(a, c):
    out = []
    for x in a:
        y = Fr(x) * c
        if y.denominator != 1:
            return None
        out.append(int(y))
    return tuple(out)


def unit(m, i):
    v = [0] * m
    v[i] = DEN
    return tuple(v)


class Solver:
    def __init__(self, m, targets, node_cap=2_000_000, deadline=None, free=()):
        self.m = m
        self.inputs = [unit(m, i) for i in range(m)] + [tuple(f) for f in free if any(f)]
        inkeys = {norm(u)[0] for u in self.inputs}
        self.targets = {norm(t)[0] for t in targets if any(t)} - inkeys
        self.node_cap = node_cap
        self.deadline = deadline
        self.nodes = 0

    # one-operation productions from the available set (keys, normalized)
    def one_op(self, avail):
        """all normalized signals producible in one operation, with a recipe."""
        out = {}
        al = list(avail)
        for i, a in enumerate(al):
            for c in SCALARS:
                s = scale(a, c)
                if s is not None:
                    k, sg = norm(s)
                    if k not in avail and k not in out:
                        out[k] = ("scale", a, c * sg)
            for b in al[i + 1:]:
                for sb, v in ((1, add(a, b)), (-1, sub(a, b))):
                    k, sg = norm(v)
                    if any(k) and k not in avail and k not in out:
                        out[k] = ("add", a, sg, b, sg * sb)
        return out

    def closure(self, avail, prog):
        """add every missing target producible in one op; returns remaining targets."""
        rem = set(self.targets) - avail
        changed = True
        while rem and changed:
            changed = False
            prods = self.one_op(avail)
            for t in list(rem):
                if t in prods:
                    avail.add(t)
                    prog.append((t, prods[t]))
                    rem.discard(t)
                    changed = True
        return rem

    def search(self, hmax):
        base = set(norm(u)[0] for u in self.inputs)
        prog0 = []
        rem = self.closure(base, prog0)
        if not rem:
            return len(self.targets), prog0
        for h in range(1, hmax + 1):
            res = self.dfs(set(base), list(prog0), h, None)
            if res is not None:
                return len(self.targets) + h, res
            if self.nodes > self.node_cap or (self.deadline and time.time() > self.deadline):
                return None
        return None

    def dfs(self, avail, prog, h, prev):
        self.nodes += 1
        if self.nodes > self.node_cap or (self.deadline and time.time() > self.deadline):
            return None
        prods = self.one_op(avail)
        rem = set(self.targets) - avail
        if h == 1:
            # the helper must make every remaining target producible next
            for k, rec in prods.items():
                if k in self.targets or (prev is not None and k < prev[0] and k in prev[1]):
                    continue
                av2 = set(avail)
                av2.add(k)
                pr2 = list(prog)
                pr2.append((k, rec))
                if not self.closure(av2, pr2):
                    return pr2
            return None
        # candidates ordered by how many remaining targets they put one op away
        def score(k):
            av2 = set(avail)
            av2.add(k)
            p2 = self.one_op(av2)
            return sum(1 for t in rem if t in p2)
        order = sorted(prods.items(), key=lambda kv: (-score(kv[0]), kv[0]))
        for k, rec in order:
            if k in self.targets or (prev is not None and k < prev[0] and k in prev[1]):
                continue
            av2 = set(avail)
            av2.add(k)
            pr2 = list(prog)
            pr2.append((k, rec))
            self.closure(av2, pr2)
            res = self.dfs(av2, pr2, h - 1, (k, prods))
            if res is not None:
                return res
            if self.nodes > self.node_cap:
                return None
        return None


def solve(m, targets, hmax=3, node_cap=2_000_000, seconds=None, free=()):
    s = Solver(m, targets, node_cap, time.time() + seconds if seconds else None, free=free)
    return s.search(hmax)


def emit_slp(m, targets_named, prog, input_names, fresh):
    """prog: list of (key, recipe); targets_named: {key: (name, sign)} for
    the outputs to be named; fresh(): generator of temporary names.
    Returns PLinOpt lines computing every named target."""
    name_of = {}
    for i in range(m):
        name_of[norm(unit(m, i))[0]] = (input_names[i], 1)
    lines = []
    for key, rec in prog:
        if key in targets_named:
            nm, sg = targets_named[key]
        else:
            nm, sg = fresh(), 1
        if rec[0] == "scale":
            _, a, c = rec
            an, asg = name_of[norm(a)[0]]
            coef = c * asg * sg
            lines.append(f"{nm}:={fmt_scale(an, coef)};")
        else:
            _, a, sa, b, sb = rec
            an, asg = name_of[norm(a)[0]]
            bn, bsg = name_of[norm(b)[0]]
            ca, cb = sa * asg * sg, sb * bsg * sg
            lines.append(f"{nm}:={fmt_sum(an, ca, bn, cb)};")
        name_of[key] = (nm, 1)
    return lines, name_of


def fmt_scale(an, c):
    c = Fr(c)
    if c.denominator == 1:
        return f"{'-' if c < 0 else ''}{abs(c.numerator)}*{an}" if abs(c) != 1 else f"{'-' if c < 0 else ''}{an}"
    return f"{'-' if c < 0 else ''}{an}/{c.denominator}" if abs(c.numerator) == 1 else f"{'-' if c < 0 else ''}{abs(c.numerator)}*{an}/{c.denominator}"


def fmt_sum(an, ca, bn, cb):
    s = ("-" if ca < 0 else "") + an + ("-" if cb < 0 else "+") + bn
    return s
