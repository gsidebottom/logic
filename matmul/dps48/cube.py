#!/usr/bin/env python3
"""Cube-and-conquer splitting for the lns48 feasibility CNFs.

    cube.py IN.cnf OUTPREFIX VAR [VAR ...]
    cube.py IN.cnf OUTPREFIX --chain VAR [VAR ...]

The first form writes 2^k CNFs OUTPREFIX_<bits>.cnf, each IN.cnf plus one unit
clause per split variable (bit 1 = positive literal), with the header's clause
count adjusted.  UNSAT on every cube proves IN.cnf UNSAT; a model of any cube
is a model of IN.cnf.

--chain writes k CNFs OUTPREFIX_c<i>.cnf partitioning "at least one of the
VARs is true": cube i has VAR_i true and VAR_1..VAR_{i-1} false.  UNSAT on
every chain cube proves IN.cnf + (VAR_1 or ... or VAR_k) UNSAT.  This is the
incremental step for a grown dictionary: if the dictionary without the new
vectors is already proven to have no closed set within the cap, a solution of
the grown one must select a new vector (the catalog lists every production
among dictionary members, so a subset's productions never depend on vectors
outside it).

With --pick K (and no VAR) it prints the K selection variables (x_v, numbered
1..D-16 in lns48's encoding) that occur most often in IN.cnf and are not
fixed by a unit clause -- the natural split variables.  D comes from lns48's
header comment, which the cube writers copy into every cube; for a file
without it pass --nx D-16.
"""
import sys
from collections import Counter


def read_cnf(path, comments=None):
    """-> (nvars, clauses); the comment lines are appended to `comments` if given."""
    header = None
    clauses = []
    with open(path) as f:
        for line in f:
            if line.startswith("c"):
                if comments is not None:
                    comments.append(line.rstrip("\n"))
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
        comments = []
        nvars, clauses = read_cnf(path, comments)
        # x_v variables: the first (D - 16) variables; D from lns48's comment header
        # (kept by the cube writers below), or --nx N for files written without it
        if "--nx" in args:
            nx = int(args[args.index("--nx") + 1])
        else:
            heads = [c for c in comments if "lns48 feasibility:" in c]
            assert heads, f"{path}: no 'lns48 feasibility' header comment; pass --nx N"
            nx = int(heads[0].split("feasibility:")[1].split()[0]) - 16
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
    chain = "--chain" in args
    if chain:
        args.remove("--chain")
    inp, prefix, vars_ = args[0], args[1], [int(v) for v in args[2:]]
    assert vars_, "no split variables given"
    comments = []
    nvars, clauses = read_cnf(inp, comments)
    # carry the input's comments (lns48's header among them) into every cube
    kept = "".join(c + "\n" for c in comments)
    body = "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
    k = len(vars_)
    if chain:
        for i, v in enumerate(vars_):
            units = [v] + [-u for u in vars_[:i]]
            with open(f"{prefix}_c{i:02d}.cnf", "w") as f:
                f.write(f"c chain cube {i} of {inp}: {v} true, {vars_[:i]} false\n")
                f.write(kept)
                f.write(f"p cnf {nvars} {len(clauses) + len(units)}\n")
                f.write(body)
                f.write("".join(f"{u} 0\n" for u in units))
        print(f"wrote {k} chain cubes {prefix}_c*.cnf (partition of 'at least one of {vars_}')")
        return
    for mask in range(1 << k):
        bits = format(mask, f"0{k}b")
        units = "".join(f"{v if bits[i] == '1' else -v} 0\n" for i, v in enumerate(vars_))
        with open(f"{prefix}_{bits}.cnf", "w") as f:
            f.write(f"c cube {bits} of {inp} on variables {vars_}\n")
            f.write(kept)
            f.write(f"p cnf {nvars} {len(clauses) + k}\n")
            f.write(body)
            f.write(units)
    print(f"wrote {1 << k} cubes {prefix}_*.cnf ({len(clauses) + k} clauses each)")


if __name__ == "__main__":
    main()
