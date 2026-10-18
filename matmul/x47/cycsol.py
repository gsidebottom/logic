#!/usr/bin/env python3
"""Decode a SAT model of cyccnf.py's cyclic quotient into a full scheme,
check every Brent equation from scratch, and write our .bits format.

Usage: cycsol.py n a b SOLVER_OUTPUT out.bits
(SOLVER_OUTPUT: kissat / cadical / cryptominisat5 output with v-lines)
"""
import sys

import pathlib  # noqa: E402
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))  # matmul/
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))  # matmul/x47
from brent import verify_bits  # noqa: E402
from cyccnf import rep_map  # noqa: E402


def read_model(path):
    val = {}
    sat = None
    for ln in open(path):
        if ln.startswith("s "):
            sat = "UNSATISFIABLE" not in ln and "SATISFIABLE" in ln
        if ln.startswith("v "):
            for tok in ln.split()[1:]:
                x = int(tok)
                if x:
                    val[abs(x)] = 1 if x > 0 else 0
    return sat, val


def main(argv):
    if len(argv) != 6:
        raise SystemExit(__doc__)
    n, a, b, sol, out = int(argv[1]), int(argv[2]), int(argv[3]), argv[4], argv[5]
    sat, val = read_model(sol)
    if not sat:
        raise SystemExit(f"{sol}: no satisfying model")
    r, rep = rep_map(n, a, b)
    nb = 3 * r * n * n
    bits = [val.get(rep[v] + 1, 0) for v in range(nb)]
    bad = verify_bits(bits, n, n, n, r)
    if bad:
        raise SystemExit(f"FAIL: {bad} Brent equations violated")
    open(out, "w").write("".join(map(str, bits)) + "\n")
    print(f"wrote {out}: <{n},{n},{n}> rank {r} ({a}x3 + {b}), all {(n * n) ** 3} Brent equations hold")


if __name__ == "__main__":
    main(sys.argv)
