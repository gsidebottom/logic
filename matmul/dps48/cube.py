#!/usr/bin/env python3
"""Cube-and-conquer splitting for the lns48 feasibility CNFs.

    cube.py IN.cnf OUTPREFIX VAR [VAR ...]

writes 2^k CNFs OUTPREFIX_<bits>.cnf, each IN.cnf plus one unit clause per
split variable (bit 1 = positive literal), with the header's clause count
adjusted.  UNSAT on every cube proves IN.cnf UNSAT; a model of any cube is a
model of IN.cnf.  With --pick K (and no VAR) it prints the K selection
variables (x_v, numbered 1..D-16 in lns48's encoding) that occur most often
in IN.cnf and are not fixed by a unit clause -- the natural split variables.
"""
import sys
from collections import Counter


def read_cnf(path):
    header = None
    clauses = []
    with open(path) as f:
        for line in f:
            if line.startswith("c"):
                continue
            if line.startswith("p cnf"):
                header = line.split()
                continue
            lits = [int(t) for t in line.split()]
            if lits and lits[-1] == 0:
                lits = lits[:-1]
            if lits:
                clauses.append(lits)
    nvars, ncl = int(header[2]), int(header[3])
    assert ncl == len(clauses), (ncl, len(clauses))
    return nvars, clauses


def main():
    args = sys.argv[1:]
    if "--pick" in args:
        k = int(args[args.index("--pick") + 1])
        path = args[0]
        nvars, clauses = read_cnf(path)
        # x_v variables: the first (D - 16) variables; read D from the comment header
        with open(path) as f:
            first = f.readline()
        d = int(first.split("feasibility:")[1].split()[0])
        nx = d - 16
        fixed = {abs(c[0]) for c in clauses if len(c) == 1}
        occ = Counter()
        for c in clauses:
            for l in c:
                v = abs(l)
                if v <= nx and v not in fixed:
                    occ[v] += 1
        best = [v for v, _ in occ.most_common(k)]
        print(" ".join(str(v) for v in best))
        print("# occurrences:", " ".join(f"{v}:{occ[v]}" for v in best), file=sys.stderr)
        return
    inp, prefix, vars_ = args[0], args[1], [int(v) for v in args[2:]]
    nvars, clauses = read_cnf(inp)
    body = "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
    k = len(vars_)
    for mask in range(1 << k):
        bits = format(mask, f"0{k}b")
        units = "".join(f"{v if bits[i] == '1' else -v} 0\n" for i, v in enumerate(vars_))
        with open(f"{prefix}_{bits}.cnf", "w") as f:
            f.write(f"c cube {bits} of {inp} on variables {vars_}\n")
            f.write(f"p cnf {nvars} {len(clauses) + k}\n")
            f.write(body)
            f.write(units)
    print(f"wrote {1 << k} cubes {prefix}_*.cnf ({len(clauses) + k} clauses each)")


if __name__ == "__main__":
    main()
