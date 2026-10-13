#!/usr/bin/env python3
"""Bit-blast an fbsmt QF_BV instance to DIMACS CNF via z3py
(simplify -> bit-blast -> tseitin-cnf; Goal.dimacs()).

Usage: fbsmt2cnf.py in.smt2 out.cnf
"""
import sys
import z3

fs = z3.parse_smt2_file(sys.argv[1])
g = z3.Goal()
for f in fs:
    g.add(f)
t = z3.Then("simplify", "bit-blast", "tseitin-cnf")
r = t(g)
assert len(r) == 1, f"{len(r)} subgoals"
open(sys.argv[2], "w").write(r[0].dimacs())
print(f"{sys.argv[2]}: {r[0].dimacs().splitlines()[0]}")
