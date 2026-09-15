"""Verify a box-engine model of a cnf2boxes translation against the original CNF.

    tools/cnf2boxes_verify.py original.cnf DIR [engine.log]

DIR is the output of tools/cnf2boxes.py (boxes.json, residual.cnf).  Runs
`sat -b boxes --boxes DIR/boxes.json < DIR/residual.cnf` (60 s) unless an
engine log with its `v` lines is given, restricts the model to the visible
variables (those of the residual clauses and the box arguments; the hidden
cone internals are free in the translation), appends them as unit clauses
to the original CNF and asks CaDiCaL whether they extend to a full model.
A bogus SAT answer — one that violates a table — shows up as UNSAT here.
"""
import sys, re, json, subprocess, pathlib
SAT = str(pathlib.Path(__file__).resolve().parent.parent / "target" / "release" / "sat")
orig, d = sys.argv[1], sys.argv[2]
if len(sys.argv) > 3:
    out = open(sys.argv[3]).read()
else:
    with open(f"{d}/residual.cnf") as f:
        p = subprocess.run([SAT, "-b", "boxes", "--boxes", f"{d}/boxes.json", "-t", "60"], stdin=f, capture_output=True, text=True)
    out = p.stdout + p.stderr
m = re.search(r"c (SAT|UNSAT|TIMEOUT)", out); print("engine:", m.group(0) if m else out[-300:])
lits = [int(x) for l in out.splitlines() if l.startswith("v ") for x in l[2:].split()]
lits = [x for x in lits if x != 0]
if not lits: print("no model"); sys.exit(0)
visible = set()
for l in open(f"{d}/residual.cnf"):
    if l.startswith(("p", "c")): continue
    visible.update(abs(int(x)) for x in l.split() if x != "0")
for inst in json.load(open(f"{d}/boxes.json")): visible.update(inst["args"])
units = [x for x in lits if abs(x) in visible]
print(f"model literals {len(lits)}, visible {len(visible)}, units added {len(units)}")
hdr = open(orig).readline().split(); nv, nc = int(hdr[2]), int(hdr[3])
tmp = f"{d}/verify.cnf"
with open(tmp, "w") as o:
    o.write(f"p cnf {nv} {nc + len(units)}\n")
    for l in open(orig):
        if not l.startswith(("p", "c")): o.write(l)
    for u in units: o.write(f"{u} 0\n")
with open(tmp) as f:
    p = subprocess.run([SAT, "-b", "cadical", "-t", "120"], stdin=f, capture_output=True, text=True)
o = p.stdout + p.stderr; m = re.search(r"c (SAT|UNSAT|TIMEOUT)[^\n]*", o)
print("original CNF + units:", m.group(0) if m else o[-300:])
