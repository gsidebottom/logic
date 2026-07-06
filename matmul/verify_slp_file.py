#!/usr/bin/env python3
"""Independent verifier for an emitted matrix-multiplication SLP.

Parses a text program of the forms
    <sym> = [-]<sym> <+|-> <sym>      (binary addition/subtraction)
    M<k>  = P<k> * Q<k>              (a product)
    <sym> = [-]<sym>                 (copy / negation, free)
    <out> = 0                        (zero form)
with inputs a11.. (n1xn2) and b11.. (n2xn3) and outputs Cij (n1xn3),
evaluates it on random integer matrices AND random non-commutative
2x2-block matrices, and confirms it computes A@B in exactly the number
of +- operations stated.  Shares no construction code with the emitter
— this is an adversarial, from-scratch check.

Usage: verify_slp_file.py FILE.slp [--dims 3,3,3,23] [--trials 3000]
"""
import re
import sys

import numpy as np


def load(path):
    return [ln.strip() for ln in open(path)
            if ln.strip() and not ln.strip().startswith("##")]


def run_program(lines, avals, bvals, anames, bnames, n1, n3, zero):
    env = dict(zip(anames, avals))
    env.update(zip(bnames, bvals))
    adds = 0
    prod = re.compile(r"^(M\d+) = (P\d+) \* (Q\d+)$")
    binop = re.compile(r"^(\S+) = (-?\S+) ([+\-]) (\S+)$")
    zed = re.compile(r"^(\S+) = 0$")
    cp = re.compile(r"^(\S+) = (-?\S+)$")

    def get(tok):
        if tok.startswith("-"):
            return -env[tok[1:]]
        return env[tok]

    for ln in lines:
        if ln.startswith("#"):
            continue
        m = prod.match(ln)
        if m:
            x, y = env[m.group(2)], env[m.group(3)]
            env[m.group(1)] = x @ y if getattr(x, "ndim", 0) == 2 else x * y
            continue
        m = binop.match(ln)
        if m:
            lhs, a, op, b = m.groups()
            env[lhs] = get(a) + get(b) if op == "+" else get(a) - get(b)
            adds += 1
            continue
        m = zed.match(ln)
        if m:
            env[m.group(1)] = zero
            continue
        m = cp.match(ln)
        if m:
            env[m.group(1)] = get(m.group(2))
            continue
        raise ValueError(f"unparsed line: {ln}")
    outs = [env[f"C{i + 1}{j + 1}"] for i in range(n1) for j in range(n3)]
    return outs, adds


def main():
    argv = sys.argv[1:]
    dims = (3, 3, 3, 23)
    trials = 3000
    if "--dims" in argv:
        i = argv.index("--dims")
        dims = tuple(int(x) for x in argv[i + 1].split(","))
        del argv[i:i + 2]
    if "--trials" in argv:
        i = argv.index("--trials")
        trials = int(argv[i + 1])
        del argv[i:i + 2]
    path = [a for a in argv if not a.startswith("--")][0]
    n1, n2, n3, r = dims
    lines = load(path)
    anames = [f"a{i + 1}{j + 1}" for i in range(n1) for j in range(n2)]
    bnames = [f"b{i + 1}{j + 1}" for i in range(n2) for j in range(n3)]

    rng = np.random.default_rng(0)
    stated = None
    for ln in lines:
        m = re.search(r"= (\d+) additions", ln)
        if m:
            stated = int(m.group(1))

    # integer trials
    add_count = None
    ok = True
    for _ in range(trials):
        A = rng.integers(-6, 7, (n1, n2))
        B = rng.integers(-6, 7, (n2, n3))
        av = [A[i, j] for i in range(n1) for j in range(n2)]
        bv = [B[i, j] for i in range(n2) for j in range(n3)]
        outs, adds = run_program(lines, av, bv, anames, bnames, n1, n3, 0)
        add_count = adds
        C = np.array(outs).reshape(n1, n3)
        if not np.array_equal(C, A @ B):
            ok = False
            break

    # non-commutative 2x2-block trials
    okn = True
    Z = np.zeros((2, 2), int)
    for _ in range(300):
        A = [[rng.integers(-3, 4, (2, 2)) for _ in range(n2)]
             for _ in range(n1)]
        B = [[rng.integers(-3, 4, (2, 2)) for _ in range(n3)]
             for _ in range(n2)]
        av = [A[i][j] for i in range(n1) for j in range(n2)]
        bv = [B[i][j] for i in range(n2) for j in range(n3)]
        outs, _ = run_program(lines, av, bv, anames, bnames, n1, n3, Z)
        for i in range(n1):
            for j in range(n3):
                exp = sum((A[i][l] @ B[l][j] for l in range(n2)), Z.copy())
                if not np.array_equal(outs[i * n3 + j], exp):
                    okn = False

    print(f"file                 : {path}")
    print(f"integer trials       : {'PASS' if ok else 'FAIL'} ({trials})")
    print(f"non-commutative 2x2  : {'PASS' if okn else 'FAIL'} (300)")
    print(f"+- operations counted: {add_count}"
          + (f"  (header states {stated})" if stated else ""))
    good = ok and okn and (stated is None or add_count == stated)
    print(f"VERDICT              : {'VERIFIED' if good else 'FAILED'}")
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
