#!/usr/bin/env python3
"""Tseitin-encode the cyclic-quotient Brent system to CNF: variables =
orbit reps (plus one aux per distinct monomial), each equation an XOR
of its monomial auxes with the right parity, via the standard XOR
ladder. kissat/cadical UNSAT would prove: no cyclic-invariant rank-23
scheme over F2 with this orbit ansatz (2 fixed summands, 7 3-orbits).

Usage: symcnf.py cyc3.map out.cnf [n1 n2 n3 r]
       (map file "identity" uses the trivial map -- the UNQUOTIENTED
       system; used by the encoder gate on known exact values)
"""
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from brent import brent_equations  # noqa: E402

MAPF, OUT = sys.argv[1], sys.argv[2]
DIMS = tuple(int(x) for x in sys.argv[3:7]) if len(sys.argv) > 6 \
    else (3, 3, 3, 23)
NB = (DIMS[0] * DIMS[1] + DIMS[1] * DIMS[2] + DIMS[0] * DIMS[2]) * DIMS[3]
if MAPF == "identity":
    rep = {v: v for v in range(NB)}
else:
    rep = {}
    for ln in open(MAPF):
        v, r = ln.split()
        rep[int(v)] = int(r)

eqs = brent_equations(*DIMS)
clauses = []
nv = NB
monvar = {}

def var_of(mon):
    global nv
    if mon not in monvar:
        nv += 1
        t = nv
        monvar[mon] = t
        x, y, z = (m + 1 for m in mon)
        clauses.append([-t, x])
        clauses.append([-t, y])
        clauses.append([-t, z])
        clauses.append([t, -x, -y, -z])
    return monvar[mon]

def xor_clause(lits, rhs):
    global nv
    # ladder: chain pairwise xor into aux vars
    cur = None
    for l in lits:
        if cur is None:
            cur = l
            continue
        nv += 1
        o = nv
        clauses.append([-o, cur, l])
        clauses.append([-o, -cur, -l])
        clauses.append([o, -cur, l])
        clauses.append([o, cur, -l])
        cur = o
    if cur is None:
        assert rhs == 0
        return
    clauses.append([cur] if rhs else [-cur])

for mons, rhs in eqs:
    lits = []
    seen = {}
    for m in mons:
        q = tuple(sorted(rep[v] for v in m))
        seen[q] = seen.get(q, 0) + 1
    for q, c in seen.items():
        if c % 2:
            lits.append(var_of(q))
    xor_clause(lits, rhs)

with open(OUT, "w") as f:
    f.write(f"p cnf {nv} {len(clauses)}\n")
    for c in clauses:
        f.write(" ".join(map(str, c)) + " 0\n")
print(f"{OUT}: {nv} vars, {len(clauses)} clauses")
