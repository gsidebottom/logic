#!/usr/bin/env python3
"""Emit the data blocks of proof/Mm/SP51Optimal.lean from Stapleton and
Perminov's certificate (matmul/external/sp51/cert.json): the three legs
(distinct nonzero rows of U, V and columns of W, mod 2), leg A's five
'helper' vectors (non-targets that are a sum of two targets in three
ways), a 2-core of each helper's sum-triple system (found by peeling),
and optimal chains for the upper bounds (fbmin certificates).

Usage: gen_sp51_optimal_data.py [fbmin]   (prints Lean to stdout)
"""
import itertools
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
FBMIN = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "..", "target", "release", "fbmin")
cert = json.load(open(os.path.join(HERE, "external", "sp51", "cert.json")))["original_matrices"]


def leg(rows):
    return sorted({int("".join(str(x % 2) for x in r), 2) for r in rows} - {0})


LEGS = {
    "A": leg(cert["U"]),
    "B": leg(cert["V"]),
    "C": leg([[cert["W"][i][m] for i in range(9)] for m in range(23)]),
}


def mat(v):
    b = format(v, "09b")
    return "!![" + "; ".join(", ".join(b[3 * i + j] for j in range(3)) for i in range(3)) + "]"


def triples(S):
    S = sorted(S)
    s = set(S)
    return [frozenset((a, b, a ^ b)) for a, b in itertools.combinations(S, 2)
            if (a ^ b) in s and a < b < (a ^ b)]


def core(S):
    """2-core of the sum-triple hypergraph of S (peel elements of degree <= 1)."""
    tr = set(triples(S))
    while True:
        deg = {}
        for t in tr:
            for x in t:
                deg[x] = deg.get(x, 0) + 1
        drop = {t for t in tr if any(deg[x] <= 1 for x in t)}
        if not drop:
            return sorted(tr, key=sorted)
        tr -= drop


def chain(rows):
    with tempfile.NamedTemporaryFile("w", suffix=".legs", delete=False) as f:
        f.write("\n".join(format(v, "09b") for v in rows) + "\n")
        path = f.name
    out = subprocess.run([FBMIN, "--tier3", "--threads", "1", path],
                         capture_output=True, text=True).stdout.splitlines()
    os.unlink(path)
    i = next(k for k, l in enumerate(out) if l.strip().startswith("basis:"))
    basis = [int(t, 2) for t in out[i].split()[1:]]
    steps = []
    for l in out[i + 1:]:
        l = l.strip()
        if not l.startswith("add "):
            break
        x, _, y, _, z = l.split()[1:]
        steps.append((int(x, 2), int(y, 2), int(z, 2)))
    seq = basis + [z for _, _, z in steps]
    for x, y, z in steps:
        assert x ^ y == z and x in seq[:seq.index(z)] and y in seq[:seq.index(z)]
    assert set(rows) <= set(seq)
    return basis, seq


def finset(vals, indent="  "):
    return "{" + (",\n" + indent).join(mat(v) for v in vals) + "}"


def vec(vals, indent="  "):
    return "![" + (",\n" + indent).join(mat(v) for v in vals) + "]"


A = LEGS["A"]
SA = set(A)
helpers = sorted(h for h in range(1, 512) if h not in SA
                 and sum(1 for x in A if (x ^ h) in SA) >= 6)
assert all(sum(1 for x in A if (x ^ h) in SA) == 6 for h in helpers)
assert all(len(triples(SA | {h})) == 12 for h in helpers)

out = []
for name, rows in LEGS.items():
    out.append(f"/-- Leg {name}: the {len(rows)} distinct nonzero "
               + {"A": "rows of `U`", "B": "rows of `V`", "C": "columns of `W`"}[name]
               + " (mod 2). -/")
    out.append(f"def leg{name} : Finset Form :=\n  " + finset(rows) + "\n")
out.append("/-- The five vectors outside leg A that are a sum of two leg-A forms in three ways. -/")
out.append("def helpersA : Finset Form :=\n  " + finset(helpers) + "\n")
for k, h in enumerate(helpers):
    K = core(SA | {h})
    assert K and all(sum(x in t for t in K) >= 2 for t in K for x in t)
    out.append(f"/-- A 2-core of the sum triples of leg A with helper {mat(h)}. -/")
    out.append(f"def coreA{k} : Finset (Finset Form) :=\n  {{"
               + ",\n   ".join("{" + ", ".join(mat(x) for x in sorted(t)) + "}" for t in K) + "}\n")
for name, rows in LEGS.items():
    basis, seq = chain(rows)
    out.append(f"/-- An optimal chain for leg {name}: nine starting forms, then "
               f"{len(seq) - 9} additions. -/")
    out.append(f"def chain{name} : Fin (9 + {len(seq) - 9}) → Form :=\n  " + vec(seq) + "\n")
print("\n".join(out))
