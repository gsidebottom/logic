"""Straight-line programs as direct sums (no common subexpressions), in PLinOpt's syntax for
gen_kernels.py --dps48: L and R map i0..i15 (row-major A or B) to o0..o47, P maps the products
i0..i47 to o0..o15 (row-major C).  Coefficients +-1 are written as signs, others as the shortest
decimal that reads back as the same double (dyadics exactly)."""
import os
import numpy as np

def term(c, var, first):
    if c == 1:
        return var if first else f"+{var}"
    if c == -1:
        return f"-{var}"
    a = repr(abs(float(c)))
    assert "e" not in a, a
    return (f"{'-' if c < 0 else ('' if first else '+')}{a}*{var}")

def program(M):
    lines = []
    for o, row in enumerate(M):
        ts = [(c, f"i{j}") for j, c in enumerate(row) if c != 0]
        assert ts, f"output {o} is zero"
        lines.append(f"o{o}:=" + "".join(term(c, v, k == 0) for k, (c, v) in enumerate(ts)) + ";")
    return "\n".join(lines) + "\n"

def write(prefix, L, R, P):
    os.makedirs(os.path.dirname(prefix), exist_ok=True)
    for nm, M in (("L", L), ("R", R), ("P", P)):
        with open(f"{prefix}_{nm}.slp", "w") as f:
            f.write(program(M))
