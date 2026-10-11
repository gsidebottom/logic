#!/usr/bin/env python3
"""Generate proof/Mm/Ring51.lean: machine-checked correctness of the
ring-valid 51-addition-per-step Karstadt-Schwartz scheme (class
i12w211c23fg, sign model 21; commit f19b943's certificates).

Pipeline (bits convention of matmul/brent.py: cell k of a 3x3 is
row-major, and C[p][q] = sum_m gamma_{m,p*3+q} * M_m -- no transpose):

  A side: 9 uncounted basis forms (signed combos of A entries, the
          unimodular basis H_U), then the 12-addition chain; product m
          uses value u_m with realized sign eps_u[m].
  B side: likewise, 13 additions, eps_v[m].
  M_m  =  (chain value)*(chain value), A factor on the left.
  Output: the C chain (12 additions) built the 23 w-rows from the
          unimodular basis H_W; the actual circuit is its TELLEGEN
          TRANSPOSE: seeds sigma_m * M_m with sigma_m = eps_u*eps_v*
          eps_w (sign absorption, free negation), reverse-DAG
          accumulation (exactly 12 + (23-9) = 26 additions), ending in
          the 9 adjoints of the basis nodes; the uncounted output
          transform is C[k] = sum_t H_W[t][k] * y_t.

Total counted additions per recursive step: 12 + 13 + 26 = 51.

The generator re-verifies the EMITTED program end-to-end over the
non-commutative word ring Z<A,B> (every output entry equals
sum_b A[p][b]B[b][q]) before writing the Lean file, and asserts the
transposed circuit has exactly 26 additions.  The emitted theorem is
hypothesis-style over a general Ring (subst_vars + noncomm_ring), in
the pattern of Mm/Correct.lean and Mm/Nielsen52.lean.

Usage: gen_ring51_lean.py ks51dir out.lean
       (ks51dir holds m21_{A,B,C}.slegs and ring51_model21.log)
"""
import pathlib, re, sys

KDIR = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "matmul/external/ks51")
OUT = pathlib.Path(sys.argv[2] if len(sys.argv) > 2 else "proof/Mm/Ring51.lean")

def read_rows(p):
    return [tuple(int(x) for x in ln.split()) for ln in open(p) if ln.strip()]

rowsA = read_rows(KDIR / "m21_A.slegs")
rowsB = read_rows(KDIR / "m21_B.slegs")
rowsC = read_rows(KDIR / "m21_C.slegs")
assert len(rowsA) == len(rowsB) == len(rowsC) == 23

# ---- parse the three certificates out of the loop log ---------------
log = open(KDIR / "ring51_model21.log").read()
blocks = {}
for nm in "ABC":
    seg = log.split(f"----- {nm} -----")[1]
    seg = seg.split("-----")[0]
    basis = [tuple(int(x) for x in m.group(1).split())
             for m in re.finditer(r"basis: ([\d\- ]+)", seg)]
    adds = []
    for m in re.finditer(r"add \[([\d\- ]+)\] ([+-]) \[([\d\- ]+)\] -> \[([\d\- ]+)\]", seg):
        x = tuple(int(v) for v in m.group(1).split())
        y = tuple(int(v) for v in m.group(3).split())
        z = tuple(int(v) for v in m.group(4).split())
        s = 1 if m.group(2) == "+" else -1
        assert tuple(a + s * b for a, b in zip(x, y)) == z
        adds.append((x, y, s, z))
    assert len(basis) == 9, (nm, len(basis))
    blocks[nm] = (basis, adds)
assert len(blocks["A"][1]) == 12 and len(blocks["B"][1]) == 13 and len(blocks["C"][1]) == 12

def neg(v):
    return tuple(-x for x in v)

def forms_of(block):
    basis, adds = block
    return basis + [z for (_, _, _, z) in adds]

def eps_of(block, rows):
    fs = forms_of(block)
    out = []
    for r in rows:
        if r in fs:
            out.append(1)
        elif neg(r) in fs:
            out.append(-1)
        else:
            raise AssertionError("row not produced by chain")
    return out

eu = eps_of(blocks["A"], rowsA)
ev = eps_of(blocks["B"], rowsB)
ew = eps_of(blocks["C"], rowsC)
sigma = [eu[i] * ev[i] * ew[i] for i in range(23)]

# ---- names -----------------------------------------------------------
def wname(leg, i):
    return f"{leg}{i}"

# map each distinct form (exact vector) of a block to a wire name
def wire_map(block, leg):
    basis, adds = block
    names, order = {}, []
    for i, b in enumerate(basis):
        names[b] = f"{leg}b{i}"
        order.append((f"{leg}b{i}", None, b))
    for i, (x, y, s, z) in enumerate(adds):
        names[z] = f"{leg}w{i}"
        order.append((f"{leg}w{i}", (names[x], names[y], s), z))
    return names, order

nA, oA = wire_map(blocks["A"], "a")
nB, oB = wire_map(blocks["B"], "b")
nC, oC = wire_map(blocks["C"], "c")

def val_name(names, row):
    if row in names:
        return names[row], 1
    return names[neg(row)], -1

# ---- Tellegen transpose of the C chain ------------------------------
# forward C: nodes cb0..cb8 (basis), cw0..cw11 (adds z = x + s*y).
# adjoint: seed each node that equals +-w_m with sigma_m * eps-sign * M_m;
# process adds in reverse: adj[x] += adj[z]; adj[y] += s*adj[z].
# Each += on a nonempty adjoint is ONE counted addition.  Result: the
# adjoints of cb0..cb8 are y_t; output C[k] = sum_t H_W[t][k] y_t.
basisC, addsC = blocks["C"]
cnodes = [nC[b] for b in basisC] + [nC[z] for (_, _, _, z) in addsC]
seeds = {n: [] for n in cnodes}   # node -> list of (sign, product index)
for m in range(23):
    # product m's output coefficient vector decomposes as
    # w_m = eps_w[m] * (chain value); with M_gen = eps_u*eps_v*M_true the
    # seed on the value node is sigma_m * M_gen (eps_w is inside sigma;
    # val_name's sign IS eps_w and must not be applied again).
    nm, sgn = val_name(nC, rowsC[m])
    assert sgn == ew[m]
    seeds[nm].append((sigma[m], m))

adj_terms = {n: list(seeds[n]) for n in cnodes}  # (sign, expr-id) lists
out_adds = []   # (target expr name, left, right, sign) emitted lets
tmp_id = 0
expr_name = {}  # node -> lean expr name of its full adjoint

def emit_sum(node, terms):
    """fold a term list into binary adds; returns final name, count."""
    global tmp_id, out_adds
    assert terms
    def term_expr(sg, m):
        return ("m%d" % (m + 1), sg) if isinstance(m, int) else (m, sg)
    (e0, s0) = term_expr(*terms[0])
    acc, acc_sign = e0, s0
    cnt = 0
    for sg, m in terms[1:]:
        (e, s) = term_expr(sg, m)
        nm = f"z{tmp_id}"
        tmp_id += 1
        # acc_sign * acc + s * e  -> normalize so stored let is plain
        if acc_sign == 1:
            out_adds.append((nm, acc, e, s))
        else:
            # -acc + s*e = -(acc - s*e)
            out_adds.append((nm, acc, e, -s))
            acc_sign = -1
        acc = nm
        cnt += 1
    return acc, acc_sign, cnt

total_out_adds = 0
for i in range(len(addsC) - 1, -1, -1):
    x, y, s, z = addsC[i]
    zn = nC[z]
    terms = adj_terms[zn]
    if not terms:
        continue
    nm, sg, c = emit_sum(zn, terms)
    total_out_adds += c
    expr_name[zn] = (nm, sg)
    adj_terms[nC[x]].append((sg, nm))
    adj_terms[nC[y]].append((s * sg, nm))

ys = []
for i, b in enumerate(basisC):
    terms = adj_terms[nC[b]]
    assert terms, "basis node with empty adjoint"
    nm, sg, c = emit_sum(nC[b], terms)
    total_out_adds += c
    ys.append((nm, sg))

assert total_out_adds == 12 + 23 - 9, f"transposed adds {total_out_adds} != 26"

# ---- exact word-ring verification of the emitted program ------------
def z_add(x, y, s=1):
    o = dict(x)
    for w, c in y.items():
        o[w] = o.get(w, 0) + s * c
        if o[w] == 0:
            del o[w]
    return o

def z_scale(k, x):
    return {w: k * c for w, c in x.items()} if k else {}

def z_mul(x, y):
    o = {}
    for w1, c1 in x.items():
        for w2, c2 in y.items():
            w = w1 + w2
            o[w] = o.get(w, 0) + c1 * c2
            if o[w] == 0:
                del o[w]
    return o

atomsA = [{(f"A{k // 3}{k % 3}",): 1} for k in range(9)]
atomsB = [{(f"B{k // 3}{k % 3}",): 1} for k in range(9)]

env = {}
for (names, order, atoms, leg) in ((nA, oA, atomsA, "a"), (nB, oB, atomsB, "b")):
    for nm, parents, vec in order:
        if parents is None:
            v = {}
            for k, co in enumerate(vec):
                if co:
                    v = z_add(v, z_scale(co, atoms[k]))
            env[nm] = v
        else:
            px, py, s = parents
            env[nm] = z_add(env[px], env[py], s)

prods = {}
for m in range(23):
    ua, sa = val_name(nA, rowsA[m])
    vb, sb = val_name(nB, rowsB[m])
    assert sa == eu[m] and sb == ev[m]
    prods[f"m{m + 1}"] = z_mul(env[ua], env[vb])

envO = dict(prods)
for nm, l, r, s in out_adds:
    envO[nm] = z_add(envO[l], envO[r], s)

want = {}
for p in range(3):
    for q in range(3):
        w = {}
        for b in range(3):
            w = z_add(w, z_mul({(f"A{p}{b}",): 1}, {(f"B{b}{q}",): 1}))
        want[p * 3 + q] = w

for k in range(9):
    got = {}
    for t, (ynm, ysg) in enumerate(ys):
        co = basisC[t][k] * ysg
        if co:
            got = z_add(got, z_scale(co, envO[ynm]))
    # fold sigma*eps corrections: already inside seeds; got must equal want
    assert got == want[k], f"output cell {k} mismatch"
print("END-TO-END WORD-RING CHECK over Z<A,B>: PASS (9/9 outputs; "
      f"adds 12+13+{total_out_adds} = {12 + 13 + total_out_adds})")

# ---- emit Lean -------------------------------------------------------
def lin_lean(vec, var):
    terms = []
    for k, co in enumerate(vec):
        if not co:
            continue
        at = f"{var}{k // 3}{k % 3}"
        if co == 1:
            terms.append(("+", at))
        elif co == -1:
            terms.append(("-", at))
        else:
            terms.append(("+", f"({co} : R) * {at}") if co > 0 else ("-", f"({-co} : R) * {at}"))
    s, first = "", True
    for sign, t in terms:
        s = (t if sign == "+" else f"-{t}") if first else f"{s} {sign} {t}"
        first = False
    return s

hyps = []
for (order, leg) in ((oA, "a"), (oB, "b")):
    var = "a" if leg == "a" else "b"
    for nm, parents, vec in order:
        if parents is None:
            hyps.append((nm, lin_lean(vec, var)))
        else:
            px, py, s = parents
            hyps.append((nm, f"{px} {'+' if s == 1 else '-'} {py}"))
for m in range(23):
    ua, sa = val_name(nA, rowsA[m])
    vb, sb = val_name(nB, rowsB[m])
    hyps.append((f"m{m + 1}", f"{ua} * {vb}"))
for nm, l, r, s in out_adds:
    hyps.append((nm, f"{l} {'+' if s == 1 else '-'} {r}"))

couts = []
for k in range(9):
    terms = []
    for t, (ynm, ysg) in enumerate(ys):
        co = basisC[t][k] * ysg
        if co == 1:
            terms.append(("+", ynm))
        elif co == -1:
            terms.append(("-", ynm))
        elif co:
            raise AssertionError("non-unit output transform entry")
    s, first = "", True
    for sign, t in terms:
        s = (t if sign == "+" else f"-{t}") if first else f"{s} {sign} {t}"
        first = False
    couts.append((f"c{k // 3 + 1}{k % 3 + 1}", s))
for nm, rhs in couts:
    hyps.append((nm, rhs))

wires = [h[0] for h in hyps]

def wrap(names, per=10, indent="     "):
    lines = [" ".join(names[i:i + per]) for i in range(0, len(names), per)]
    return ("\n" + indent).join(lines)

hyp_lines = "\n".join(f"    (h{w} : {w} = {rhs})" for w, rhs in hyps)
concl = " ∧\n".join(
    f"      c{i}{j} = a{i - 1}{0} * b{0}{j - 1} + a{i - 1}{1} * b{1}{j - 1} + a{i - 1}{2} * b{2}{j - 1}"
    for i in range(1, 4) for j in range(1, 4))

out = f"""/-
Copyright (c) 2026 Greg Sidebottom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom
-/
import Mathlib.Tactic.NoncommRing

/-!
# 51 additions per recursive step for rank-23 3×3 multiplication

Machine-checked correctness of the ring-valid Karstadt–Schwartz-style
scheme on HKS class `i12w211c23fg`, sign model 21 (found by the exact
signed free-basis search `fbsmin`/`fbsloop`; certificates in
`matmul/external/ks51/`).  Generated by `matmul/gen_ring51_lean.py`,
which replays the emitted program over the word ring ℤ⟨A,B⟩ before
writing this file.

Counted additions per recursive step: **12 (A side) + 13 (B side) +
26 (output, the Tellegen transpose of a 12-addition chain plus the
23−9 fan-in) = 51**, one below the 52 of arXiv 2609.06588, in the same
alternative-basis cost model.  The three basis changes (`a b0..a b8`,
`b b0..b b8` inputs, and the `c*`-combination output transform) are the
uncounted, amortized transforms; all are unimodular.

The statement is over a general, not-necessarily-commutative ring: each
product keeps its A-side factor on the left, so the scheme recurses on
block matrices.  Variables `a00..a22`, `b00..b22` are the entries
(row-major); `c11..c33` the outputs.
-/

namespace Ring51

variable {{R : Type _}} [Ring R]

set_option maxHeartbeats 1600000 in
-- subst_vars inlines ~120 wires; each output is one large noncomm_ring
-- goal, which exceeds the default heartbeat budget.
/-- The 51-addition-per-step scheme computes `A · B` over any ring. -/
theorem correct
    (a00 a01 a02 a10 a11 a12 a20 a21 a22
     b00 b01 b02 b10 b11 b12 b20 b21 b22 : R)
    ({wrap(wires)} : R)
{hyp_lines} :
{concl} := by
  subst_vars
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> noncomm_ring

end Ring51

-- Axiom audit: a valid proof shows only Lean's standard axioms.
#print axioms Ring51.correct
"""

OUT.write_text(out)
print(f"wrote {OUT} ({len(out.splitlines())} lines, {len(wires)} wires)")
