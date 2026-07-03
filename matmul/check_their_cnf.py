#!/usr/bin/env python3
"""Plant one of our schemes (a `b <bits>` line / raw bitstring) into a
Heule matrix-challenges CNF as base-var units and run kissat — independent
confirmation that the scheme satisfies THEIR exact instance.

Usage: python3 check_their_cnf.py their.cnf bits.txt
Exit 0 iff kissat says SATISFIABLE.
"""
import subprocess
import sys
import tempfile

from brent import var_counts

NA, NB, _ = var_counts(3, 3, 3, 23)


def to_their(v):
    """our var (0-based, block order alpha/beta/gamma) -> their var
    (1-based, summand-major 27-blocks, gamma transposed)."""
    if v < NA:
        m, off = divmod(v, 9)
        return 27 * m + 1 + off
    if v < NA + NB:
        m, off = divmod(v - NA, 9)
        return 27 * m + 10 + off
    m, off = divmod(v - NA - NB, 9)
    i, j = divmod(off, 3)
    return 27 * m + 19 + 3 * j + i


def main():
    cnf, bitsfile = sys.argv[1], sys.argv[2]
    txt = open(bitsfile).read().split()
    bits = [int(c) for c in (txt[1] if txt[0] == "b" else txt[0]).strip()]
    assert len(bits) == 621
    lines = open(cnf).read().splitlines()
    header = next(l for l in lines if l.startswith("p cnf"))
    _, _, nv, nc = header.split()
    units = [f"{to_their(v) if b else -to_their(v)} 0"
             for v, b in enumerate(bits)]
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {nv} {int(nc) + len(units)}\n")
        for l in lines:
            if not l.startswith(("p", "c")):
                f.write(l + "\n")
        f.write("\n".join(units) + "\n")
        path = f.name
    r = subprocess.run(["kissat", "-q", path], capture_output=True, text=True)
    sat = any(l == "s SATISFIABLE" for l in r.stdout.splitlines())
    print(f"{cnf}: {'SATISFIED by our scheme' if sat else 'NOT satisfied'}")
    sys.exit(0 if sat else 1)


if __name__ == "__main__":
    main()
