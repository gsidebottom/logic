#!/usr/bin/env python3
"""Convert an lns48 feasibility CNF to pseudo-Boolean OPB with a NATIVE cardinality
constraint, for cutting-planes solvers (RoundingSat) that reason about
"at most cap of the selection variables" directly instead of through the
clausal sequential counter that CDCL solvers resolve over.

    cnf2opb.py IN.cnf OUT.opb

lns48 writes its variables in blocks -- x_v (D-16 of them, first), y_p, levels,
then the Sinz counter registers (last (D-16)*cap variables) -- and a header
comment "c lns48 feasibility: D vectors (16 inputs), P productions, cap C, lmax L".
Every clause mentioning a counter register is dropped and replaced by the single
constraint  -x_1 - ... - x_{D-16} >= -C.  Clauses become  sum(lits) >= 1  with a
negative literal ~x written as (1 - x), i.e. -1 x on the left and -1 on the right.
"""
import re
import sys


def main():
    inp, out = sys.argv[1], sys.argv[2]
    header = None
    clauses = []
    meta = None
    with open(inp) as f:
        for line in f:
            if line.startswith("c lns48 feasibility"):
                m = re.search(r"(\d+) vectors \((\d+) inputs\), (\d+) productions, cap (\d+), (lmax \d+|order)", line)
                g = m.groups()
                meta = tuple(int(x) for x in g[:4]) + (g[4],)
                continue
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
    assert meta, "not an lns48 feasibility CNF (header comment missing)"
    d, ninp, nprod, cap, lmax = meta
    nvars = int(header[2])
    nx = d - ninp
    assert nx > cap, "no counter block when D-16 <= cap"
    first_counter = nvars - nx * cap + 1
    kept = [c for c in clauses if all(abs(l) < first_counter for l in c)]
    dropped = len(clauses) - len(kept)
    # sanity: the counter block is exactly the clauses touching registers; all other
    # clauses use only variables below the block
    assert dropped > 0
    lines = []
    for c in kept:
        terms = []
        rhs = 1
        for l in c:
            if l > 0:
                terms.append(f"+1 x{l}")
            else:
                terms.append(f"-1 x{-l}")
                rhs -= 1
        lines.append(" ".join(terms) + f" >= {rhs} ;")
    card = " ".join(f"-1 x{v}" for v in range(1, nx + 1)) + f" >= -{cap} ;"
    lines.append(card)
    with open(out, "w") as f:
        f.write(f"* #variable= {first_counter - 1} #constraint= {len(lines)}\n")
        f.write(f"* from {inp}: {d} vectors, {nprod} productions, cap {cap}, {lmax}; "
                f"{dropped} counter clauses replaced by one cardinality constraint\n")
        f.write("\n".join(lines) + "\n")
    print(f"wrote {out}: {first_counter - 1} variables, {len(lines)} constraints "
          f"({len(kept)} clauses + cardinality; dropped {dropped} counter clauses over {nx * cap} registers)")


if __name__ == "__main__":
    main()
