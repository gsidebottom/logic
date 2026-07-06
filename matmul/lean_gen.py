#!/usr/bin/env python3
"""Generate a Lean 4 proof that the 55-addition scheme computes A*B.

Source of truth: ../src/mm55.rs (the verified Rust transcription of
external/i19-55adds-slp.txt).  We parse its `let NAME = EXPR;` lines,
(1) pre-verify correctness in pure Python over a *non-commutative*
polynomial ring -- every monomial is exactly (one a-var)*(one b-var),
kept in a-before-b order, so no commutativity is ever assumed -- and
(2) emit a Lean theorem stating each output equals the matrix-product
entry over a general `Ring R`, proven by `subst_vars; noncomm_ring`.

The Lean file is a *faithful* transcription (the 78 intermediate wires
appear as hypotheses), so Lean itself -- not this script -- does the
algebraic verification.  This script only transcribes and sanity-checks.
"""
import re, sys, pathlib

RS = pathlib.Path(__file__).with_name("..") / "src" / "mm55.rs"
RS = (pathlib.Path(__file__).parent.parent / "src" / "mm55.rs").resolve()
OUT = pathlib.Path(__file__).parent / "mm55proof" / "Mm55proof" / "Correct.lean"

BASE_A = [f"a{i}{j}" for i in range(1,4) for j in range(1,4)]
BASE_B = [f"b{i}{j}" for i in range(1,4) for j in range(1,4)]

# ---- parse the SLP: ordered list of (name, rust_expr) ----
def parse_slp():
    defs = []
    for line in RS.read_text().splitlines():
        line = re.sub(r"//.*", "", line).strip()      # strip comments
        m = re.match(r"let\s+(aw\d+|bw\d+|m\d+|cw\d+)\s*=\s*(.+?);", line)
        if m:
            defs.append((m.group(1), m.group(2).strip()))
    return defs

# ---- non-commutative polynomial: dict {monomial-tuple: int} ----
# monomial is a tuple of atom names IN ORDER (never sorted -> no commutativity)
def padd(p, q, s=1):
    r = dict(p)
    for mono, c in q.items():
        r[mono] = r.get(mono, 0) + s*c
        if r[mono] == 0: del r[mono]
    return r
def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            mono = m1 + m2                 # concatenate, order preserved
            r[mono] = r.get(mono, 0) + c1*c2
            if r[mono] == 0: del r[mono]
    return r

# ---- tokenizer + recursive-descent evaluator over the wire table ----
def tokenize(e):
    return re.findall(r"[A-Za-z_]\w*|[-+*()]", e)

class P:
    def __init__(self, toks, table):
        self.t, self.i, self.tab = toks, 0, table
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def eat(self):
        x = self.t[self.i]; self.i += 1; return x
    def expr(self):                        # expr := term (('+'|'-') term)*
        v = self.term()
        while self.peek() in ("+", "-"):
            op = self.eat(); v = padd(v, self.term(), 1 if op=="+" else -1)
        return v
    def term(self):                        # term := factor ('*' factor)*
        v = self.factor()
        while self.peek() == "*":
            self.eat(); v = pmul(v, self.factor())
        return v
    def factor(self):                      # factor := '-' factor | NAME | '(' expr ')'
        if self.peek() == "-":
            self.eat(); return padd({}, self.factor(), -1)
        if self.peek() == "(":
            self.eat(); v = self.expr(); assert self.eat() == ")"; return v
        name = self.eat()
        return self.tab[name]              # substitute wire's expanded poly

def evaluate(defs):
    tab = {v: {(v,): 1} for v in BASE_A + BASE_B}   # base atoms
    for name, expr in defs:
        tab[name] = P(tokenize(expr), tab).expr()
    return tab

# ---- main ----
defs = parse_slp()
tab = evaluate(defs)

# operation counts (sanity): each aw/bw/cw line = (#tokens of + or -) adds;
# unary '-(' is free (negation); each m line = 1 mul
adds = muls = 0
for name, expr in defs:
    if name.startswith("m"):
        muls += 1
    else:
        # count binary +/-: total +/- minus the unary ones (a '-' right after
        # '=' start or right after '(' is unary)
        toks = tokenize(expr)
        for k,tk in enumerate(toks):
            if tk == "+":
                adds += 1
            elif tk == "-":
                if k == 0 or toks[k-1] in ("(",):    # unary negation -> free
                    pass
                else:
                    adds += 1
print(f"parsed {len(defs)} wire defs; counted {muls} multiplications, {adds} additions")
assert muls == 23, muls
assert adds == 55, adds

OUTS = ["cw11","cw13","cw14","cw16","cw18","cw21","cw23","cw25","cw27"]
def matmul_poly(I, J):
    return {(f"a{I}{K}", f"b{K}{J}"): 1 for K in (1,2,3)}

ok = True
for p, cw in enumerate(OUTS):
    I, J = p//3 + 1, p%3 + 1
    got, want = tab[cw], matmul_poly(I, J)
    match = got == want
    ok &= match
    print(f"  C{I}{J} = {cw}: {'OK' if match else 'MISMATCH'}"
          + ("" if match else f"\n     got  {got}\n     want {want}"))
if not ok:
    print("PRE-CHECK FAILED"); sys.exit(1)
print("PRE-CHECK PASSED: all 9 outputs equal the matrix product (non-commutative)")

# ---- emit Lean ----
def lean_expr(e):    # rust expr -> lean expr (identical operator syntax)
    return re.sub(r"\s+", " ", e).strip()

wires = [n for n,_ in defs]
def wrap(names, per=12, indent="     "):
    groups = [names[i:i+per] for i in range(0, len(names), per)]
    return ("\n"+indent).join(" ".join(g) for g in groups)
sig_inputs = " ".join(BASE_A) + "\n     " + " ".join(BASE_B)
sig_wires  = wrap(wires)
hyps = "\n".join(f"    (h{n} : {n} = {lean_expr(e)})" for n,e in defs)
goals = []
for p, cw in enumerate(OUTS):
    I, J = p//3 + 1, p%3 + 1
    rhs = " + ".join(f"a{I}{K} * b{K}{J}" for K in (1,2,3))
    goals.append(f"      {cw} = {rhs}")
goal_block = " ∧\n".join(goals)
refine = "⟨" + ", ".join("?_" for _ in OUTS) + "⟩"

lean = f'''\
/-
Copyright (c) 2026 Greg Sidebottom and Claude Fable 5. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom, Claude Fable 5
-/
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# The 55-addition, 23-multiplication scheme computes 3×3 matrix multiplication

Machine-checked correctness of the rank-23 scheme of de Groote class
`i19w225c4efh` (fewer additions than any previously published rank-23
3×3 scheme; the prior record was 56).  Generated from `src/mm55.rs`
by `matmul/lean_gen.py`.

The statement is over a **general, not-necessarily-commutative** ring
`R`: every product keeps its left factor on the left, so this certifies
a genuine bilinear algorithm that applies recursively to block matrices.
The 78 intermediate wires (`aw*`, `bw*`, `m*`, `cw*`) are the exact
straight-line program; `subst_vars` inlines them and `noncomm_ring`
verifies each of the 9 outputs equals `∑ₖ aᵢₖ bₖⱼ`.
-/

namespace Matmul55

variable {{R : Type _}} [Ring R]

/-- Each of the 9 outputs of the 55-addition scheme equals the
corresponding entry of the matrix product `A · B`, over any ring. -/
theorem correct
    ({sig_inputs} : R)
    ({sig_wires} : R)
{hyps} :
{goal_block} := by
  subst_vars
  refine {refine} <;> (first | noncomm_ring | abel)

end Matmul55

-- Axiom audit: elaborating this prints the axiom dependencies; a valid
-- proof shows only Lean's standard axioms (no `sorryAx`).
#print axioms Matmul55.correct
'''
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(lean)
print(f"wrote {OUT}  ({len(lean.splitlines())} lines)")

# ---- emit the idiomatic Matrix-API corollary: scheme A B = A * B ----
def rc(v):    # a11 -> (0,0) as Fin 3 indices
    return int(v[1])-1, int(v[2])-1
entry_lets = "\n".join(
    f"  let {v} := {'A' if v[0]=='a' else 'B'} {rc(v)[0]} {rc(v)[1]}"
    for v in BASE_A + BASE_B)
wire_lets = "\n".join(f"  let {n} := {lean_expr(e)}" for n,e in defs)
mat = (f"  !![{OUTS[0]}, {OUTS[1]}, {OUTS[2]};\n"
       f"     {OUTS[3]}, {OUTS[4]}, {OUTS[5]};\n"
       f"     {OUTS[6]}, {OUTS[7]}, {OUTS[8]}]")
OUT2 = OUT.parent / "Matrix.lean"
lean2 = f'''\
/-
Copyright (c) 2026 Greg Sidebottom and Claude Fable 5. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom, Claude Fable 5
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# The 55-addition scheme equals the Mathlib matrix product

`scheme A B` runs the 55-addition, 23-multiplication straight-line
program on two `3×3` matrices over any ring `R`, and `scheme_eq_mul`
proves it equals Mathlib's own matrix product `A * B`.  This packages
`Matmul55.correct` in Mathlib's native `Matrix` API.
-/

namespace Matmul55

variable {{R : Type _}} [Ring R]

/-- The 55-addition, 23-multiplication scheme as a map on `3×3`
matrices: the exact straight-line program of `src/mm55.rs`, reading the
inputs from `A`, `B` and assembling the 9 outputs into a matrix. -/
def scheme (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
{entry_lets}
{wire_lets}
{mat}

-- `scheme` unfolds to a ~100-binding straight-line program, so a single
-- elaboration exceeds the default heartbeat budget; raise it for this proof.
set_option maxHeartbeats 1600000 in
-- Plain `simp` (below) evaluates the concrete `!![..] i j` indexing via
-- Mathlib's matrix simprocs; the explicit `simp only` lemma set for this is
-- version-fragile, so we accept the flexible-`simp` lint here.
set_option linter.flexible false in
/-- The scheme computes the matrix product, in Mathlib's own terms. -/
theorem scheme_eq_mul (A B : Matrix (Fin 3) (Fin 3) R) :
    scheme A B = A * B := by
  simp only [scheme]                    -- unfold the SLP once (not per goal)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | noncomm_ring | abel

end Matmul55

#print axioms Matmul55.scheme_eq_mul
'''
OUT2.write_text(lean2)
print(f"wrote {OUT2}  ({len(lean2.splitlines())} lines)")
