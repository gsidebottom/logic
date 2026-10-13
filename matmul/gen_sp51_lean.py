#!/usr/bin/env python3
"""Generate proof/Mm/SP51.lean: machine-checked correctness of the
Stapleton--Perminov 51-addition alternative-basis scheme, verbatim from
their published verification listing (arXiv:2609.32388; stored at
matmul/external/sp51/sp51_published.py with their cert.json).

The generator parses their multiply3x3_cr51 straight-line program
line-by-line (SSA-renaming the two reused variables u22, v12), replays
it over the non-commutative word ring Z<A,B> (all 9 outputs must equal
sum_k A[i][k]B[k][j]), checks their basis matrices P, Q, R are
unimodular (the KS amortization requirement), and asserts the published
addition accounting before emitting Lean:

  UNCOUNTED input conversions: 1 (A side) + 3 (B side)
  COUNTED kernel:              13 (u chain) + 12 (v chain) + 26 (output)
  UNCOUNTED output conversion: 1
  => 51 per recursive step, 56 one-shot.

The emitted theorems mirror Mm/Ring51.lean: hypothesis-style `correct`
(subst_vars + noncomm_ring) and the Matrix-API pair
`rank23_add51_scheme` / `rank23_add51_scheme_eq_mul`, namespaced SP51.

Usage: gen_sp51_lean.py [spdir] [out.lean]
"""
import json
import pathlib
import re
import sys
from fractions import Fraction

SPDIR = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "matmul/external/sp51")
OUT = pathlib.Path(sys.argv[2] if len(sys.argv) > 2 else "proof/Mm/SP51.lean")

src = (SPDIR / "sp51_published.py").read_text()
body = src.split("def multiply3x3_cr51", 1)[1]
body = body.split("return c.reshape(3, 3)", 1)[0]

# ---- parse the straight-line program ---------------------------------
IDENT = r"[a-z]\d+[a-z]?"

def parse_terms(expr):
    """'p11 - p10 + p6' -> [(1,'p11'), (-1,'p10'), (1,'p6')]"""
    toks = re.findall(rf"({IDENT})|([+\-*])", expr)
    out, sign, saw_mul = [], 1, False
    for name, op in toks:
        if op == "+":
            sign = 1
        elif op == "-":
            sign = -1
        elif op == "*":
            saw_mul = True
        else:
            out.append((sign, name))
            sign = 1
    return out, saw_mul

ops = []            # {'lhs','kind','terms','sect'}
outputs = None      # list of 9 term-lists
assign_count = {}
reassigned = set()
for raw in body.splitlines():
    ln = raw.split("#")[0].strip()
    if not ln or "=" not in ln or ".reshape(9)" in ln:
        continue
    lhs, rhs = (s.strip() for s in ln.split("=", 1))
    if lhs == "c":
        inner = rhs[rhs.index("[") + 1:rhs.rindex("]")]
        outputs = [parse_terms(e)[0] for e in inner.split(",")]
        assert len(outputs) == 9
        continue
    lhss = [s.strip() for s in lhs.split(",")]
    rhss = [s.strip() for s in rhs.split(",")] if len(lhss) > 1 else [rhs]
    assert len(lhss) == len(rhss), ln
    for l, r in zip(lhss, rhss):
        terms, is_mul = parse_terms(r)
        kind = "mul" if is_mul else "lin"
        if kind == "mul":
            assert len(terms) == 2 and all(s == 1 for s, _ in terms), ln
        ops.append({"lhs": l, "kind": kind, "terms": terms})
        assign_count[l] = assign_count.get(l, 0) + 1

reassigned = {v for v, c in assign_count.items() if c > 1}
assert reassigned == {"u22", "v12"}, reassigned

# SSA rename: first assignment of a reused name gets the 'a' suffix;
# RHS references resolve through the current map in program order.
cur = {}
for op in ops:
    op["terms"] = [(s, cur.get(n, n)) for s, n in op["terms"]]
    l = op["lhs"]
    if l in reassigned and l not in cur:
        op["lhs"] = l + "a"
        cur[l] = l + "a"
    else:
        cur[l] = l
outputs = [[(s, cur.get(n, n)) for s, n in terms] for terms in outputs]

def sect_of(lhs):
    return {"x": "xconv", "y": "yconv", "u": "uchain", "v": "vchain",
            "p": "prods", "t": "outstage", "z": "outstage"}[lhs[0]]

adds = {}
for op in ops:
    op["sect"] = sect_of(op["lhs"])
    if op["kind"] == "lin":
        adds[op["sect"]] = adds.get(op["sect"], 0) + len(op["terms"]) - 1
adds["outconv"] = sum(len(t) - 1 for t in outputs)
expect = {"xconv": 1, "yconv": 3, "uchain": 13, "vchain": 12,
          "outstage": 26, "outconv": 1}
assert adds == expect, adds
assert sum(1 for op in ops if op["kind"] == "mul") == 23
print("addition accounting: counted 13+12+26 = 51, uncounted 1+3+1 = 5")

# ---- unimodularity of their basis matrices ---------------------------
cert = json.load(open(SPDIR / "cert.json"))

def det(M):
    A = [[Fraction(x) for x in row] for row in M]
    n, d = len(A), Fraction(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            if A[i][c] != 0:
                f = A[i][c] / A[c][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return d

for nm in ("P", "Q", "R"):
    dv = det(cert["basis"][nm])
    assert abs(dv) == 1, (nm, dv)
print("basis matrices P, Q, R all unimodular (|det| = 1)")

# ---- word-ring verification over Z<A,B> ------------------------------
def z_add(x, y, s=1):
    o = dict(x)
    for w, c in y.items():
        o[w] = o.get(w, 0) + s * c
        if o[w] == 0:
            del o[w]
    return o

def z_mul(x, y):
    o = {}
    for w1, c1 in x.items():
        for w2, c2 in y.items():
            w = w1 + w2
            o[w] = o.get(w, 0) + c1 * c2
            if o[w] == 0:
                del o[w]
    return o

env = {}
for k in range(9):
    env[f"a{k}"] = {(f"A{k // 3}{k % 3}",): 1}
    env[f"b{k}"] = {(f"B{k // 3}{k % 3}",): 1}
for op in ops:
    if op["kind"] == "mul":
        (_, un), (_, vn) = op["terms"]
        assert un[0] == "u" and vn[0] == "v", op   # A factor stays left
        env[op["lhs"]] = z_mul(env[un], env[vn])
    else:
        v = {}
        for s, n in op["terms"]:
            v = z_add(v, env[n], s)
        env[op["lhs"]] = v
for k, terms in enumerate(outputs):
    got = {}
    for s, n in terms:
        got = z_add(got, env[n], s)
    want = {}
    for b in range(3):
        want = z_add(want, z_mul({(f"A{k // 3}{b}",): 1},
                                 {(f"B{b}{k % 3}",): 1}))
    assert got == want, f"output cell {k} mismatch"
print("END-TO-END WORD-RING CHECK over Z<A,B>: PASS (9/9 outputs)")

# ---- emit Lean -------------------------------------------------------
def entry(nm, style):
    # a7 -> 'a21' (hyp style) or 'A 2 1' (matrix style)
    k = int(nm[1:])
    return (f"{nm[0]}{k // 3}{k % 3}" if style == "hyp"
            else f"{nm[0].upper()} {k // 3} {k % 3}")

def rhs_str(terms, style, kind="lin"):
    if kind == "mul":
        return f"{terms[0][1]} * {terms[1][1]}"
    s, first = "", True
    for sg, n in terms:
        e = entry(n, style) if re.fullmatch(r"[ab]\d", n) else n
        if style == "def" and sg == -1 and " " in e:
            e = f"({e})"
        if first:
            s = e if sg == 1 else f"-{e}"
            first = False
        else:
            s += f" {'+' if sg == 1 else '-'} {e}"
    return s

SECT_HDR = {
    "xconv": ("  -- A-side basis change (UNCOUNTED, amortized): x = P·vec A,\n"
              "  -- applied once per matrix; 1 addition"),
    "yconv": "  -- B-side basis change (UNCOUNTED): y = Q·vec B; 3 additions",
    "uchain": "  -- A-side chain: 13 COUNTED additions (paid per recursive step)",
    "vchain": "  -- B-side chain: 12 COUNTED additions",
    "prods": "  -- the 23 products (A factor on the left: recurses on blocks)",
    "outstage": ("  -- output stage: 26 COUNTED additions (their published\n"
                 "  -- 12-addition output leg in transposed, 12+14-add form)"),
}
hyps, def_lines, last_sect = [], [], None
for op in ops:
    if op["sect"] != last_sect:
        def_lines.append(SECT_HDR[op["sect"]])
        last_sect = op["sect"]
    hyps.append((op["lhs"], rhs_str(op["terms"], "hyp", op["kind"])))
    def_lines.append(f"  let {op['lhs']} := "
                     f"{rhs_str(op['terms'], 'def', op['kind'])}")
def_lines.append("  -- output basis change (UNCOUNTED): vec C = R·z; 1 addition")
couts = []
for k, terms in enumerate(outputs):
    cn = f"c{k // 3 + 1}{k % 3 + 1}"
    couts.append((cn, rhs_str(terms, "hyp")))
    def_lines.append(f"  let {cn} := {rhs_str(terms, 'def')}")
hyps.extend(couts)

wires = [h[0] for h in hyps]
def wrap(names, per=10, indent="     "):
    lines = [" ".join(names[i:i + per]) for i in range(0, len(names), per)]
    return ("\n" + indent).join(lines)

hyp_lines = "\n".join(f"    (h{w} : {w} = {rhs})" for w, rhs in hyps)
concl = " ∧\n".join(
    f"      c{i}{j} = a{i - 1}{0} * b{0}{j - 1} + a{i - 1}{1} * b{1}{j - 1} + a{i - 1}{2} * b{2}{j - 1}"
    for i in range(1, 4) for j in range(1, 4))
def_body = "\n".join(def_lines)
mat_rows = ";\n     ".join(
    ", ".join(f"c{i}{j}" for j in range(1, 4)) for i in range(1, 4))

out = f"""/-
Copyright (c) 2026 Greg Sidebottom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/-!
# The Stapleton–Perminov 51-addition scheme, machine-checked

Correctness of the alternative-basis rank-23 3×3 scheme of Stapleton
and Perminov (arXiv:2609.32388), transcribed verbatim from the
verification listing in their paper
(`matmul/external/sp51/sp51_published.py`, with their certificate
`cert.json`); their reused variables `u22`, `v12` are SSA-renamed
`u22a`, `v12a`.  Generated by `matmul/gen_sp51_lean.py`, which replays
the program over the word ring ℤ⟨A,B⟩ and checks their basis matrices
`P`, `Q`, `R` are unimodular before writing this file.

Counted additions per recursive step: **13 (u chain) + 12 (v chain) +
26 (output stage) = 51**; the conversions (`x8`, `y2`, `y6`, `y8`, and
the final `z8 + z2`) cost 1+3+1 = 5 uncounted additions — their
one-shot flat total is 56, the cheapest known complete 51-package.
Their scheme lies in HKS class `i12w219c23ci-008` (family
`17x2+52x+4y6+5y4+14y3+z32+2z27`, the family of all four known
51-classes); our exact search proves legs 13+12+12 and conversions
1+3+1 are both optimal for the class (`fbmin`/`fbsmin` tiers).

The statement is over a general, not-necessarily-commutative ring:
each product keeps its A-side factor on the left, so the scheme
recurses on block matrices.

**To run this proof** (force a genuine re-elaboration — a plain
`lake build` replays the cached result of the last build):

```
cd proof && find .lake/build -name "SP51.*" -delete && lake build Mm.SP51
```

Expect `Built Mm.SP51` (not `Replayed`), followed by the two
`#print axioms` lines below — `[propext]` for `correct` and the three
standard axioms for `rank23_add51_scheme_eq_mul`, with no `sorryAx`.
A fresh checkout needs `lake exe cache get` in `proof/` once.
-/

namespace SP51

variable {{R : Type _}} [Ring R]

set_option maxHeartbeats 1600000 in
-- subst_vars inlines ~130 wires; each output is one large noncomm_ring
-- goal, which exceeds the default heartbeat budget.
/-- The Stapleton–Perminov 51-addition-per-step scheme computes `A · B`
over any ring. -/
theorem correct
    (a00 a01 a02 a10 a11 a12 a20 a21 a22
     b00 b01 b02 b10 b11 b12 b20 b21 b22 : R)
    ({wrap(wires)} : R)
{hyp_lines} :
{concl} := by
  subst_vars
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (first | noncomm_ring | abel)

/-- The Stapleton–Perminov scheme as a map on `3×3` matrices, in the
structure of `Ring51.rank23_add51_scheme`: UNCOUNTED unimodular input
conversions (1 and 3 additions), the COUNTED 13- and 12-addition input
chains, the 23 products, the COUNTED 26-addition output stage, and the
UNCOUNTED 1-addition output conversion.  Counted additions per
recursive step: 13 + 12 + 26 = **51**; one-shot flat total 56. -/
def rank23_add51_scheme (A B : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
{def_body}
  !![{mat_rows}]

-- `rank23_add51_scheme` unfolds to a ~130-binding straight-line
-- program; a single elaboration exceeds the default heartbeat budget.
set_option maxHeartbeats 1600000 in
-- Plain `simp` evaluates the concrete `!![..] i j` indexing via
-- Mathlib's matrix simprocs; the explicit lemma set is version-fragile,
-- so the flexible-`simp` lint is accepted here (as in Mm/Matrix.lean).
set_option linter.flexible false in
/-- The scheme computes the matrix product, in Mathlib's own terms. -/
theorem rank23_add51_scheme_eq_mul (A B : Matrix (Fin 3) (Fin 3) R) :
    rank23_add51_scheme A B = A * B := by
  simp only [rank23_add51_scheme]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    (first | noncomm_ring | abel)

end SP51

-- Axiom audit: a valid proof shows only Lean's standard axioms.
#print axioms SP51.correct
#print axioms SP51.rank23_add51_scheme_eq_mul
"""

OUT.write_text(out)
print(f"wrote {OUT} ({len(out.splitlines())} lines, {len(wires)} wires)")
