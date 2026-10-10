#!/usr/bin/env python3
"""Generate proof/Mm/Nielsen52.lean: machine-checked correctness of
Nielsen's 52-addition, 23-multiplication Karstadt-Schwartz-style scheme
for 3x3 matrix multiplication (arXiv 2609.06588).

Scheme data transcribed from the paper's ancillary small_verify.py.
The pipeline is  vec(C) = BW^-1 . W'( (U'(BU^-1 vec A)) .* (V'(BV^-1 vec B)) )
with BU, BV, BW unimodular {-1,0,1} matrices whose inverses are again
{-1,0,1}, U'/V' 12-addition chains, W' a 28-addition chain: 52 additions
in the alternative basis (the paper's count); the three basis changes
cost extra additions outside that count (row-wise as presented: 6+3+4).

Every wire is built as a tiny AST, evaluated BOTH into Lean source text
and into the exact non-commutative ring Z<A,B> (words with integer
coefficients); the 9 emitted outputs are asserted equal to A.B before
anything is written.  The emitted theorems follow Mm/Correct.lean and
Mm/Matrix.lean conventions (subst_vars + noncomm_ring/abel; Matrix API
wrapper; #print axioms audit).
"""
from fractions import Fraction
import sys, pathlib

# ---------------------------------------------------------------- data
BU = [
    [0, -1, 0, 0, -1, 0, 0, 0, 0],
    [0,  1, 0, 0,  0, 0, 1, 0, 0],
    [0,  0, 0, 0,  1, 0, 0, 0, 0],
    [0,  0, 0, 0,  0, 0, 0, 0, -1],
    [0,  0, 0, -1, 0, 0, 0, 0, 0],
    [0,  0, 0, 1,  0, 0, 0, 1, 1],
    [1,  0, 0, 0,  0, -1, 0, 0, 0],
    [0,  0, 1, 0,  0, 0, 0, 0, 0],
    [0,  0, 0, 0,  0, 1, 0, 0, 0],
]
BV = [
    [0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 1, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, 0, 1, 0],
]
BW = [
    [0, 0,  0, 0,  0,  0,  0, 1, 0],
    [0, 0, -1, 0,  0,  0,  0, 0, 1],
    [0, 1,  0, 0,  0,  0,  0, 0, 0],
    [0, 0, -1, 0,  0,  0,  0, 0, 0],
    [0, 0,  0, 1,  0,  0,  0, 0, 0],
    [0, 1,  0, 0,  1, -1,  0, 0, 0],
    [0, 0,  0, 0, -1,  0,  0, 0, 0],
    [1, 0,  0, 0,  0,  0, -1, 0, 0],
    [0, 0,  0, 0,  0,  0, -1, 0, 0],
]

# u-chain over the primed A entries ap0..ap8 (= A'11..A'33 row-major):
# (wire, op, x, y) with x/y wire names; slots map product index -> operand.
U_CHAIN = [
    ("u1", "+", "ap2", "ap6"), ("u2", "-", "ap5", "ap8"),
    ("u3", "-", "ap0", "u2"), ("u4", "+", "ap1", "ap4"),
    ("u9", "+", "ap0", "u1"), ("u10", "+", "ap1", "u1"),
    ("u11", "-", "ap7", "u2"), ("u17", "-", "ap3", "ap1"),
    ("u13", "-", "ap6", "u17"), ("u15", "-", "u11", "ap2"),
    ("u19", "+", "ap3", "u11"), ("u23", "+", "ap7", "u17"),
]
U_SLOT = {1: "u1", 2: "u2", 3: "u3", 4: "u4", 5: "ap8", 6: "u3", 7: "u4",
          8: "ap8", 9: "u9", 10: "u10", 11: "u11", 12: "ap2", 13: "u13",
          14: "ap3", 15: "u15", 16: "ap6", 17: "u17", 18: "ap4", 19: "u19",
          20: "ap5", 21: "ap7", 22: "ap1", 23: "u23"}

V_CHAIN = [
    ("v1", "-", "bp3", "bp1"), ("v2", "+", "bp7", "v1"),
    ("v4", "-", "bp8", "bp2"), ("v7", "-", "bp5", "v2"),
    ("v10", "-", "bp0", "v1"), ("v11", "+", "bp0", "bp4"),
    ("v17", "-", "bp8", "bp3"), ("v13", "+", "bp4", "v17"),
    ("v15", "+", "bp8", "v11"), ("v18", "-", "bp6", "v2"),
    ("v19", "-", "bp6", "v11"), ("v23", "-", "bp7", "v17"),
]
V_SLOT = {1: "v1", 2: "v2", 3: "bp5", 4: "v4", 5: "v4", 6: "bp2", 7: "v7",
          8: "v7", 9: "bp1", 10: "v10", 11: "v11", 12: "bp0", 13: "v13",
          14: "bp4", 15: "v15", 16: "bp3", 17: "v17", 18: "v18", 19: "v19",
          20: "v18", 21: "bp8", 22: "bp7", 23: "v23"}

S_CHAIN = [
    ("s1", "-", "m7", "m16"), ("s2", "-", "m1", "m12"),
    ("s3", "-", "m14", "m5"), ("s4", "-", "m8", "m2"),
    ("s5", "-", "m17", "m8"), ("s6", "+", "m13", "m4"),
    ("s7", "+", "m22", "s1"), ("s8", "-", "m16", "s2"),
    ("s9", "-", "s3", "m21"), ("s10", "-", "s4", "m20"),
    ("s11", "+", "m21", "s5"), ("s12", "+", "m14", "s6"),
    ("s13", "-", "m10", "s8"), ("s14", "-", "m9", "s8"),
    ("s15", "-", "s10", "m11"), ("s16", "-", "s10", "m12"),
    ("s17", "+", "m22", "s11"), ("s18", "+", "m16", "s12"),
    ("s19", "+", "m18", "s13"), ("s20", "-", "s14", "m20"),
    ("s21", "-", "m14", "s15"), ("s22", "-", "s16", "m3"),
    ("s23", "+", "m6", "s16"), ("s24", "+", "m23", "s17"),
    ("s25", "+", "m17", "s18"), ("s26", "+", "m19", "s21"),
    ("s27", "-", "s23", "m15"), ("s28", "-", "m19", "s27"),
]
WP = ["s24", "s20", "s26", "s22", "s25", "s28", "s9", "s19", "s7"]  # w'1..w'9

# ------------------------------------------------- exact linear algebra
def mat_inv(M):
    n = len(M)
    A = [[Fraction(M[i][j]) for j in range(n)]
         + [Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    out = [[x for x in row[n:]] for row in A]
    assert all(x.denominator == 1 and abs(x) <= 1 for row in out for x in row), \
        "inverse not {-1,0,1}-integral"
    return [[int(x) for x in row] for row in out]

BUi, BVi, BWi = mat_inv(BU), mat_inv(BV), mat_inv(BW)

# --------------------------------------- exact ring Z<A,B> (dict words)
def z_add(x, y, s=1):
    out = dict(x)
    for w, c in y.items():
        out[w] = out.get(w, 0) + s * c
        if out[w] == 0:
            del out[w]
    return out

def z_mul(x, y):
    out = {}
    for w1, c1 in x.items():
        for w2, c2 in y.items():
            w = w1 + w2
            out[w] = out.get(w, 0) + c1 * c2
            if out[w] == 0:
                del out[w]
    return out

# ----------------------------------------------- build wires (text+value)
a_names = [f"a{i}{j}" for i in range(1, 4) for j in range(1, 4)]
b_names = [f"b{i}{j}" for i in range(1, 4) for j in range(1, 4)]
env = {n: {(n,): 1} for n in a_names + b_names}

hyps = []   # (wire, rhs_lean)

def lin_text(row, names):
    terms = []
    for k, nm in zip(row, names):
        if k == 1:
            terms.append(("+", nm))
        elif k == -1:
            terms.append(("-", nm))
        elif k != 0:
            raise AssertionError("coefficient outside {-1,0,1}")
    s, first = "", True
    for sign, nm in terms:
        if first:
            s = nm if sign == "+" else f"-{nm}"
            first = False
        else:
            s += f" {sign} {nm}"
    return s

def lin_val(row, names):
    out = {}
    for k, nm in zip(row, names):
        if k:
            out = z_add(out, env[nm], k)
    return out

for i in range(9):
    for pre, Bi, names in (("ap", BUi, a_names), ("bp", BVi, b_names)):
        w = f"{pre}{i}"
        hyps.append((w, lin_text(Bi[i], names)))
        env[w] = lin_val(Bi[i], names)

for w, op, x, y in U_CHAIN + V_CHAIN:
    hyps.append((w, f"{x} {op} {y}"))
    env[w] = z_add(env[x], env[y], 1 if op == "+" else -1)

for k in range(1, 24):
    w = f"m{k}"
    hyps.append((w, f"{U_SLOT[k]} * {V_SLOT[k]}"))
    env[w] = z_mul(env[U_SLOT[k]], env[V_SLOT[k]])

for w, op, x, y in S_CHAIN:
    hyps.append((w, f"{x} {op} {y}"))
    env[w] = z_add(env[x], env[y], 1 if op == "+" else -1)

c_wires = []
for i in range(3):          # row
    for j in range(3):      # column; vec(C) is column-major: row 3*j+i
        w = f"c{i+1}{j+1}"
        row = BWi[3 * j + i]
        hyps.append((w, lin_text(row, WP)))
        env[w] = lin_val(row, WP)
        c_wires.append((w, i, j))

# ------------------------------------------------------- gate: C = A.B
for w, i, j in c_wires:
    want = {(f"a{i+1}{k}", f"b{k}{j+1}"): 1 for k in range(1, 4)}
    assert env[w] == want, f"emitted program wrong at {w}"
print("emitted-program exact check over Z<A,B>: PASS (9/9 outputs)")

# ------------------------------------------------------------- emission
wires = [h[0] for h in hyps]

def wrap(names, per=12, indent="     "):
    lines, cur = [], []
    for n in names:
        cur.append(n)
        if len(cur) == per:
            lines.append(" ".join(cur)); cur = []
    if cur:
        lines.append(" ".join(cur))
    return ("\n" + indent).join(lines)

hyp_lines = "\n".join(f"    (h{w} : {w} = {rhs})" for w, rhs in hyps)
concl = " ∧\n".join(
    f"      c{i}{j} = a{i}1 * b1{j} + a{i}2 * b2{j} + a{i}3 * b3{j}"
    for i in range(1, 4) for j in range(1, 4))

# Matrix-API wrapper pieces -------------------------------------------------
def entry(pre, k):           # vec index -> Lean matrix entry, row-major
    M = "A" if pre == "a" else "B"
    return f"{M} {k // 3} {k % 3}"

def lin_text_M(row, pre):
    terms = []
    for k, c in enumerate(row):
        if c == 1:
            terms.append(("+", entry(pre, k)))
        elif c == -1:
            terms.append(("-", entry(pre, k)))
    s, first = "", True
    for sign, nm in terms:
        if first:
            s = nm if sign == "+" else f"-({nm})"
            first = False
        else:
            s += f" {sign} {nm}"
    return s

ap_lets = "\n".join(f"    let ap{i} := {lin_text_M(BUi[i], 'a')}" for i in range(9))
bp_lets = "\n".join(f"    let bp{i} := {lin_text_M(BVi[i], 'b')}" for i in range(9))
u_lets = "\n".join(f"    let {w} := {x} {op} {y}" for w, op, x, y in U_CHAIN)
v_lets = "\n".join(f"    let {w} := {x} {op} {y}" for w, op, x, y in V_CHAIN)
m_lets = "\n".join(f"    let m{k} := {U_SLOT[k]} * {V_SLOT[k]}" for k in range(1, 24))
s_lets = "\n".join(f"    let {w} := {x} {op} {y}" for w, op, x, y in S_CHAIN)

def lin_text_W(row):
    terms = []
    for k, c in enumerate(row):
        if c == 1:
            terms.append(("+", WP[k]))
        elif c == -1:
            terms.append(("-", WP[k]))
    s, first = "", True
    for sign, nm in terms:
        if first:
            s = nm if sign == "+" else f"-{nm}"
            first = False
        else:
            s += f" {sign} {nm}"
    return s

c_exprs = {(i, j): lin_text_W(BWi[3 * j + i]) for i in range(3) for j in range(3)}
c_rows = ";\n     ".join(
    ", ".join(c_exprs[(i, j)] for j in range(3)) for i in range(3))

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
# Nielsen's 52-addition alternative-basis scheme computes 3×3 matmul

Machine-checked correctness of the rank-23 Karstadt–Schwartz-style
scheme of Hugo Nielsen, "A 52-Addition, Rank-23 Scheme for Exact 3x3
Matrix Multiplication" (arXiv:2609.06588); data transcribed from the
paper's ancillary `small_verify.py` and generated by
`matmul/gen_nielsen52_lean.py`, which re-verifies the emitted program
exactly over the non-commutative ring ℤ⟨A,B⟩ before writing this file.

The pipeline is
  `vec C = BW⁻¹ ∘ W' ∘ (⊙23) ∘ (U' × V') ∘ (BU⁻¹ × BV⁻¹) (vec A, vec B)`
where `BU, BV, BW` are unimodular with all of `B·` and `B·⁻¹` having
entries in `{{-1, 0, 1}}`, `U'`/`V'` are 12-addition chains, and `W'` is a
28-addition chain.  **Cost model**: the paper's 52 = 12 + 12 + 28 counts
additions in the alternative basis only; the basis changes
`BU⁻¹/BV⁻¹/BW⁻¹` cost further additions (row-wise as presented: 6, 3
and 4), which Karstadt–Schwartz accounting amortizes across recursion
levels.  This differs from the flat (no-basis-change) model of
`Mm/Correct.lean`'s 55-addition record, so the two counts are not
comparable.

The statement is over a **general, not-necessarily-commutative** ring:
every product keeps its `A`-side factor on the left, so this certifies a
genuine bilinear algorithm that applies recursively to block matrices.
-/

namespace Nielsen52

variable {{R : Type _}} [Ring R]

set_option maxHeartbeats 1600000 in
-- `subst_vars` inlines the ~100 wires, making each of the 9 outputs one
-- large `noncomm_ring` goal; the default budget does not cover all nine.
/-- Each of the 9 outputs of the 52-addition alternative-basis scheme
equals the corresponding entry of `A · B`, over any ring.  Wires:
`ap*`/`bp*` are the basis-changed inputs `BU⁻¹ vec A` / `BV⁻¹ vec B`,
`u*`/`v*` the 12+12 input-side additions, `m1..m23` the products,
`s1..s28` the output-side additions, and `c* ` the entries of
`BW⁻¹` applied to the designated `s`-wires. -/
theorem correct
    (a11 a12 a13 a21 a22 a23 a31 a32 a33
     b11 b12 b13 b21 b22 b23 b31 b32 b33 : R)
    ({wrap(wires)} : R)
{hyp_lines} :
{concl} := by
  subst_vars
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-- The 52-addition alternative-basis scheme as a map on `3×3` matrices:
basis-changed inputs (`ap*`, `bp*`), the 12+12 input-side additions, the
23 multiplies, the 28 output-side additions, and the `BW⁻¹` output
basis change. -/
def scheme (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  -- A-side basis change (not counted in the 52)
{ap_lets}
  -- B-side basis change (not counted in the 52)
{bp_lets}
  -- 12 adds on the A side
{u_lets}
  -- 12 adds on the B side
{v_lets}
  -- 23 multiplies
{m_lets}
  -- 28 adds on the output side
{s_lets}
  -- output basis change BW⁻¹ (not counted in the 52)
  !![{c_rows}]

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
    noncomm_ring

end Nielsen52

-- Axiom audit: a valid proof shows only Lean's standard axioms (no
-- `sorryAx`).
#print axioms Nielsen52.correct
#print axioms Nielsen52.scheme_eq_mul
"""

dst = pathlib.Path(__file__).resolve().parent.parent / "proof" / "Mm" / "Nielsen52.lean"
dst.write_text(out)
print(f"wrote {dst} ({len(out.splitlines())} lines)")
