#!/usr/bin/env python3
"""nondyadic.py: what constants that are not powers of two cost a level (2026-11-14).

Product k of a scheme can be rescaled, S_k -> a_k S_k, T_k -> b_k T_k, M_k -> M_k / (a_k b_k) in
the output program: the same scheme, the same growth factor (the products |u_k| |v_k| |w_k| do not
change), other constants.  With a_k, b_k powers of two nothing changes in floating point; with
3, 1/3, 5/7, ... every coefficient of the three programs becomes a constant that is rounded
itself and whose multiplication rounds.  The difference in the measured error is the cost of
non-dyadic constants alone, which is what a rank record over Q with such constants would pay on
top of its growth factor.

Writes the R levels' direct-sum programs (schemes/r336, r363, r633) rescaled, into
schemes/nd/VARIANT/ (with the T levels' files copied, which the generator also reads):
  ctl   a = b = 1: the same programs through this writer (i/2 becomes i*0.5): must reproduce rdirect
  p2    a_k, b_k random powers of two in 1/4 .. 4: must reproduce rdirect's errors (exact scalings)
  nd3   a = 3, b = 1/3 for every product (the output program keeps its 0, +-1 coefficients... times 1)
  ndr   a_k, b_k random in {1/3, 3/5, 5/7, 7/5, 5/3, 3}: every program non-dyadic, constants mixed in every sum
"""
import os, re, random, shutil, sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
TERM = re.compile(r"([+-]?)i(\d+)(?:/(\d+))?")

def read(path):
    """-> (comment, rows): rows[o] = {input: coefficient}"""
    rows, head = {}, ""
    for ln in open(path):
        ln = ln.strip()
        if ln.startswith("#"): head = ln; continue
        if not ln: continue
        lhs, rhs = ln.rstrip(";").split(":=")
        assert lhs[0] == "o" and TERM.sub("", rhs) == "", f"not a direct sum: {ln}"
        rows[int(lhs[1:])] = {int(i): Fr(-1 if s == "-" else 1, int(d or 1)) for s, i, d in TERM.findall(rhs)}
    return head, [rows[k] for k in range(len(rows))]

def write(path, head, rows, note):
    out = [head + " -- " + note]
    for o, row in enumerate(rows):
        s = ""
        for i, q in sorted(row.items()):
            sign = "-" if q < 0 else ("+" if s else "")
            s += f"{sign}i{i}" + ("" if abs(q) == 1 else f"*{float(abs(q))!r}")
        out.append(f"o{o}:={s};")
    open(path, "w").write("\n".join(out) + "\n")

def variant(name, pick):
    d = os.path.join(HERE, "schemes", "nd", name)
    os.makedirs(d, exist_ok=True)
    for lev in ("r336", "r363", "r633"):
        (hl, L), (hr, R), (hp, P) = (read(os.path.join(HERE, "schemes", f"{lev}_{s}.slp")) for s in "LRP")
        rng = random.Random(f"{name}/{lev}")
        ab = [pick(rng) for _ in L]
        assert len(L) == len(R) == len(ab)
        note = f"rescaled by nondyadic.py, variant {name}"
        write(os.path.join(d, f"{lev}_L.slp"), hl, [{i: q * a for i, q in row.items()} for row, (a, b) in zip(L, ab)], note)
        write(os.path.join(d, f"{lev}_R.slp"), hr, [{i: q * b for i, q in row.items()} for row, (a, b) in zip(R, ab)], note)
        write(os.path.join(d, f"{lev}_P.slp"), hp, [{k: q / (ab[k][0] * ab[k][1]) for k, q in row.items()} for row in P], note)
        nz = sum(len(r) for t in (L, R, P) for r in t)
        print(f"{name}/{lev}: {len(L)} products, {nz} coefficients")
    for f in os.listdir(os.path.join(HERE, "schemes")):
        if f.startswith("t") and f.endswith(".slp"): shutil.copy(os.path.join(HERE, "schemes", f), d)

ND = [Fr(1, 3), Fr(3, 5), Fr(5, 7), Fr(7, 5), Fr(5, 3), Fr(3)]
P2 = [Fr(1, 4), Fr(1, 2), Fr(2), Fr(4)]
variant("ctl", lambda r: (Fr(1), Fr(1)))
variant("p2", lambda r: (r.choice(P2), r.choice(P2)))
variant("nd3", lambda r: (Fr(3), Fr(1, 3)))
variant("ndr", lambda r: (r.choice(ND), r.choice(ND)))
