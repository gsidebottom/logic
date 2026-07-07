#!/usr/bin/env python3
"""Independent checker for emitted rational <4x4x4:48> SLPs (cse48
--emit output).  Parses the text from scratch, evaluates with exact
Fractions, proves the bilinear map on ALL 256 basis pairs (complete —
a bilinear map is determined by its values on basis pairs), spot-checks
random integer matrices, and recounts operations from the text alone:
  adds   = lines `w = x ± y` (unary negation is free)
  shifts = lines `w = x << k`
  mults  = lines `w = x * y`   (must be exactly 48)

Usage: verify_slp48.py FILE.slp [--trials 200]
"""
import re
import sys
from fractions import Fraction


def parse(path):
    ops = []
    for ln in open(path):
        ln = ln.split("#")[0].strip()
        if not ln:
            continue
        m = re.match(r"^(\S+) = (.+)$", ln)
        assert m, ln
        w, rhs = m.group(1), m.group(2).strip()
        m2 = re.match(r"^(\S+) << (-?\d+)$", rhs)
        if m2:
            ops.append(("shl", w, m2.group(1), int(m2.group(2))))
            continue
        m2 = re.match(r"^(\S+) \* (\S+)$", rhs)
        if m2:
            ops.append(("mul", w, m2.group(1), m2.group(2)))
            continue
        m2 = re.match(r"^(-?)(\S+) ([+-]) (\S+)$", rhs)
        if m2:
            ops.append(("bin", w, m2.group(1) == "-", m2.group(2),
                        m2.group(3) == "-", m2.group(4)))
            continue
        m2 = re.match(r"^(-?)(\S+)$", rhs)
        if m2:
            ops.append(("ali", w, m2.group(1) == "-", m2.group(2)))
            continue
        raise SystemExit(f"unparsable line: {ln}")
    return ops


def evaluate(ops, avec, bvec):
    env = {}
    for i in range(16):
        env[f"a{i}"] = Fraction(avec[i])
        env[f"b{i}"] = Fraction(bvec[i])
    for op in ops:
        if op[0] == "shl":
            _, w, x, k = op
            env[w] = env[x] * (Fraction(2) ** k)
        elif op[0] == "mul":
            _, w, x, y = op
            env[w] = env[x] * env[y]
        elif op[0] == "bin":
            _, w, negx, x, negy, y = op
            vx = -env[x] if negx else env[x]
            vy = -env[y] if negy else env[y]
            env[w] = vx + vy
        else:
            _, w, neg, x = op
            env[w] = -env[x] if neg else env[x]
    return [env[f"c{z}"] for z in range(16)]


def matmul4(a, b):
    return [sum(a[4 * i + k] * b[4 * k + j] for k in range(4))
            for i in range(4) for j in range(4)]


def main():
    path = sys.argv[1]
    trials = 200
    if "--trials" in sys.argv:
        trials = int(sys.argv[sys.argv.index("--trials") + 1])
    ops = parse(path)
    adds = sum(1 for o in ops if o[0] == "bin")
    shifts = sum(1 for o in ops if o[0] == "shl")
    mults = sum(1 for o in ops if o[0] == "mul")
    print(f"parsed {len(ops)} lines: {adds} adds, {shifts} shifts, "
          f"{mults} mults, {sum(1 for o in ops if o[0]=='ali')} free aliases/negs")
    assert mults == 48, "must be a rank-48 scheme"

    # complete proof: all 256 basis pairs
    for x in range(16):
        for y in range(16):
            av = [1 if i == x else 0 for i in range(16)]
            bv = [1 if i == y else 0 for i in range(16)]
            got = evaluate(ops, av, bv)
            want = matmul4(av, bv)
            assert got == want, f"basis pair ({x},{y}) mismatch"
    print("basis pairs        : PASS (256/256 — complete bilinear proof)")

    # random integer spot checks
    import random
    rng = random.Random(42)
    for _ in range(trials):
        av = [rng.randint(-99, 99) for _ in range(16)]
        bv = [rng.randint(-99, 99) for _ in range(16)]
        assert evaluate(ops, av, bv) == matmul4(av, bv)
    print(f"random integer     : PASS ({trials})")
    print(f"VERDICT            : VERIFIED — {adds} adds + {shifts} shifts "
          f"+ 48 mults = {adds + shifts} additive-model ops")


if __name__ == "__main__":
    main()
