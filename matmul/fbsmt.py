#!/usr/bin/env python3
"""SMT attack on the free-vector-basis gap of the signed KS leg
problem: does a signed addition chain with `a` additions exist that
computes all 23 target rows (up to sign) from NINE ARBITRARY bounded
integer basis vectors -- not just 9-target bases (fbsmin's scope)?

Encoding (QF_BV, width 6, every form's entries constrained to
[-M, M] with 2M strictly inside the width so adds cannot wrap):
  g_0..g_8          basis vectors, entries in [-B, B];
  f_9..f_{8+a}      chain values; step t picks operands via one-hot
                    selectors over earlier forms and a sign bit:
                    f_t = f_i + f_j  or  f_i - f_j;
  coverage          for each distinct target (up to sign) some form
                    equals +-target.
Symmetry breaking: each basis vector's first nonzero entry positive;
basis vectors lexicographically nondecreasing.

Unimodularity of the basis is NOT encoded (integer determinants are
hostile to BV encodings); it is checked on the decoded model, and on
failure the caller re-runs with a blocking clause (--block file).

Modes:
  gen   slegs a B out.smt2 [blockfile]   write the instance
  check slegs a z3out                    decode a z3 model, replay the
                                         chain exactly, report basis
                                         |det| (1 = ring-valid as-is)

An UNSAT verdict is a bounded-impossibility: no chain with entries
bounded by M (helpers included) and basis entries bounded by B exists.
Report it with the bounds; it does not by itself exclude larger
coefficients.

Usage:
  fbsmt.py gen   leg.slegs 13 2 out.smt2 [block.smt2]
  fbsmt.py check leg.slegs 13 z3.out
"""
import sys
from fractions import Fraction

W = 6          # bit width
M = 12         # |entry| bound for every form (2M+? < 2^(W-1) = 32)

def read_rows(path):
    rows = []
    for ln in open(path):
        if ln.strip():
            v = tuple(int(x) for x in ln.split())
            assert len(v) == 9
            rows.append(v)
    return rows

def canon(v):
    for x in v:
        if x:
            return tuple(-e for e in v) if x < 0 else v
    return v

def reps_of(rows):
    out = []
    for r in rows:
        c = canon(r)
        if c not in out:
            out.append(c)
    return out

def bv(x):
    return f"(_ bv{x & ((1 << W) - 1)} {W})"

def gen(slegs, a, B, out, blockfile=None):
    reps = reps_of(read_rows(slegs))
    d = len(reps)
    nf = 9 + a
    L = []
    L.append("(set-logic QF_BV)")
    for t in range(nf):
        for c in range(9):
            L.append(f"(declare-fun f{t}c{c} () (_ BitVec {W}))")
    # range constraint helper: -lim <= x <= lim  (signed)
    def inrange(x, lim):
        return f"(and (bvsle {bv(-lim)} {x}) (bvsle {x} {bv(lim)}))"
    # basis bounds + symmetry: first nonzero positive, lex order
    for t in range(9):
        for c in range(9):
            L.append(f"(assert {inrange(f'f{t}c{c}', B)})")
        nz = []
        for c in range(9):
            pz = " ".join(f"(= f{t}c{k} {bv(0)})" for k in range(c)) or "true"
            nz.append(f"(and {pz} (bvsgt f{t}c{c} {bv(0)}))")
        allz = " ".join(f"(= f{t}c{k} {bv(0)})" for k in range(9))
        L.append(f"(assert (or {' '.join(nz)}))")
        _ = allz
    for t in range(8):
        # lex <= between basis t and t+1 (coarse: first coord)
        L.append(f"(assert (bvsle f{t}c0 f{t + 1}c0))")
    # chain steps
    for t in range(9, nf):
        for i in range(t):
            L.append(f"(declare-fun l{t}_{i} () Bool)")
            L.append(f"(declare-fun r{t}_{i} () Bool)")
        L.append(f"(declare-fun s{t} () Bool)")
        onehot_l = " ".join(f"l{t}_{i}" for i in range(t))
        onehot_r = " ".join(f"r{t}_{i}" for i in range(t))
        L.append(f"(assert (or {onehot_l}))")
        L.append(f"(assert (or {onehot_r}))")
        for i in range(t):
            for j in range(i + 1, t):
                L.append(f"(assert (not (and l{t}_{i} l{t}_{j})))")
                L.append(f"(assert (not (and r{t}_{i} r{t}_{j})))")
        for c in range(9):
            xi = f"x{t}c{c}"
            yi = f"y{t}c{c}"
            L.append(f"(declare-fun {xi} () (_ BitVec {W}))")
            L.append(f"(declare-fun {yi} () (_ BitVec {W}))")
            for i in range(t):
                L.append(f"(assert (=> l{t}_{i} (= {xi} f{i}c{c})))")
                L.append(f"(assert (=> r{t}_{i} (= {yi} f{i}c{c})))")
            L.append(f"(assert (= f{t}c{c} (ite s{t} (bvadd {xi} {yi}) (bvsub {xi} {yi}))))")
        for c in range(9):
            L.append(f"(assert {inrange(f'f{t}c{c}', M)})")
    # coverage: every rep appears up to sign among all forms
    for k, r in enumerate(reps):
        opts = []
        for t in range(nf):
            eqp = " ".join(f"(= f{t}c{c} {bv(r[c])})" for c in range(9))
            eqn = " ".join(f"(= f{t}c{c} {bv(-r[c])})" for c in range(9))
            opts.append(f"(and {eqp})")
            opts.append(f"(and {eqn})")
        L.append(f"(assert (or {' '.join(opts)}))")
    if blockfile:
        L.extend(ln.rstrip() for ln in open(blockfile) if ln.strip())
    L.append("(check-sat)")
    L.append("(get-model)")
    with open(out, "w") as f:
        f.write("\n".join(L) + "\n")
    print(f"{out}: d={d} targets, a={a} adds, basis |entries|<={B}, "
          f"form bound {M}, {nf} forms")

def parse_model(z3out):
    import re
    vals = {}
    txt = open(z3out).read()
    first = txt.split("\n")[0].strip()
    if first == "unsat":
        return None
    if first in ("timeout", "unknown") or first != "sat":
        print(f"no verdict: solver said '{first}'")
        sys.exit(3)
    for m in re.finditer(r"\(define-fun (f\d+c\d+) \(\) \(_ BitVec \d+\)\s+#([bx])([0-9a-f]+)\)", txt):
        name, kind, digits = m.groups()
        v = int(digits, 2 if kind == "b" else 16)
        if v >= 1 << (W - 1):
            v -= 1 << W
        vals[name] = v
    return vals

def check(slegs, a, z3out):
    rows = read_rows(slegs)
    reps = reps_of(rows)
    vals = parse_model(z3out)
    if vals is None:
        print("unsat (bounded impossibility at these bounds)")
        return
    nf = 9 + a
    forms = []
    for t in range(nf):
        forms.append(tuple(vals.get(f"f{t}c{c}", 0) for c in range(9)))
    # replay: each chain form must be x +- y of earlier forms
    for t in range(9, nf):
        okstep = any(
            forms[t] == tuple(p + s * q for p, q in zip(forms[i], forms[j]))
            for i in range(t) for j in range(t) if i != j for s in (1, -1)
        )
        assert okstep, f"step {t} is not a +- of earlier forms"
    for r in reps:
        assert any(canon(f) == r for f in forms), f"target {r} missing"
    # basis determinant
    A = [[Fraction(x) for x in forms[t]] for t in range(9)]
    det = Fraction(1)
    for c in range(9):
        p = next((i for i in range(c, 9) if A[i][c] != 0), None)
        if p is None:
            det = Fraction(0)
            break
        if p != c:
            A[c], A[p] = A[p], A[c]
            det = -det
        det *= A[c][c]
        for i in range(c + 1, 9):
            if A[i][c] != 0:
                fct = A[i][c] / A[c][c]
                A[i] = [x - fct * y for x, y in zip(A[i], A[c])]
    print(f"SAT: chain replays exactly; {a} adds; basis |det| = {abs(det)}"
          f" ({'ring-valid as-is' if abs(det) == 1 else 'needs det blocking + rerun'})")
    for t in range(9):
        print("  basis:", forms[t])
    for t in range(9, nf):
        print("  form :", forms[t])

if __name__ == "__main__":
    if sys.argv[1] == "gen":
        gen(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5],
            sys.argv[6] if len(sys.argv) > 6 else None)
    elif sys.argv[1] == "check":
        check(sys.argv[2], int(sys.argv[3]), sys.argv[4])
    else:
        sys.exit("mode must be gen or check")
