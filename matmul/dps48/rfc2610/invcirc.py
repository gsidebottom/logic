#!/usr/bin/env python3
"""Sedoglavic's question: are the known circuits invariant under the stabilizer?  An element can only
preserve a program of the same cost if it permutes the program's inputs up to sign, so per side the
elements that matter are those acting by signed permutations on that side's two modes: L (X, Y),
R (Y, Z), P (Z, X).  Each program is a set of 16-dimensional forms up to scale; P is read through its
transposed program.  Counts how many internal forms land on forms of the program it maps to.

  invcirc.py NAME STAB.json L.sms L.slp R.sms R.slp P.sms Pt.slp
"""
import json, sys
from fractions import Fraction as Fr
D = '/Users/greg/projects/logic/matmul/dps48'; sys.path.insert(0, D)
import slp48check as C
name, st, Ls, Lp, Rs, Rp, Ps, Pp = sys.argv[1:9]
def forms(path):
    env = {f"i{k}": {k: Fr(1)} for k in range(16)}; out = {}
    for lhs, rhs in C.parse(open(path).read()):
        v, _ = C.linear(rhs, env); env[lhs] = v; out[lhs] = [v.get(k, Fr(0)) for k in range(16)]
    return out
def sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = [[Fr(0)] * c for _ in range(r)]
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1][int(t[1]) - 1] = Fr(t[2])
    return M
def key(v):
    f = next((x for x in v if x), None); return None if f is None else tuple(x / f for x in v)
def mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def T(A): return [list(r) for r in zip(*A)]
def inv(M):
    A = [list(r) + [Fr(i == j) for j in range(4)] for i, r in enumerate(M)]
    for c in range(4):
        p = next(r for r in range(c, 4) if A[r][c]); A[c], A[p] = A[p], A[c]
        d = A[c][c]; A[c] = [x / d for x in A[c]]
        for r in range(4):
            if r != c and A[r][c]:
                f = A[r][c]; A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [r[4:] for r in A]
def rs(v): return [list(v[i * 4:i * 4 + 4]) for i in range(4)]
def vec(M): return tuple(x for r in M for x in r)
units = {key([Fr(i == j) for j in range(16)]) for i in range(16)}
LM, RM, PM = sms(Ls), sms(Rs), sms(Ps); Pc = [list(c) for c in zip(*PM)]
prog, outs = {}, {}
for side, path, target in (("L", Lp, LM), ("R", Rp, RM), ("P", Pp, Pc)):
    f = forms(path); o = {key(r) for r in target} - {None}
    S = {key(v) for v in f.values()} - {None}
    assert o <= S | units, f"{side} program misses outputs: {len(o - S - units)}"
    prog[side] = S - units; outs[side] = o - units
print(f"{name}: internal forms L {len(prog['L'] - outs['L'])}, R {len(prog['R'] - outs['R'])}, P^T {len(prog['P'] - outs['P'])}; outputs L {len(outs['L'])}, R {len(outs['R'])}, P^T {len(outs['P'])}")
el = json.load(open(st))
F = lambda m: [[Fr(x) for x in r] for r in m]
res = {}
for e in el:
    X, Y, Z = F(e['X']), F(e['Y']), F(e['Z']); Xi, Yi, Zi = inv(X), inv(Y), inv(Z)
    id_ = e['slot'] == 'id'
    mx, my, mz = e['mono']
    if id_ and e['pi'] == list(range(48)): continue
    acts = {"L": (lambda s: mm(mm(X, rs(s)), Yi), "L", mx and my) if id_ else (lambda s: mm(mm(Y, T(rs(s))), Zi), "R", mx and my and mz),
            "R": (lambda s: mm(mm(Y, rs(s)), Zi), "R", my and mz) if id_ else (lambda s: mm(mm(X, T(rs(s))), Yi), "L", mx and my and mz),
            "P": (lambda s: T(mm(mm(Z, T(rs(s))), Xi)) if id_ else T(mm(mm(Z, rs(s)), Xi)), "P", mz and mx)}
    if not id_: acts["P"] = (lambda s: T(mm(mm(Z, rs(s)), Xi)), "P", mz and mx)
    else:       acts["P"] = (lambda s: T(mm(mm(Z, T(rs(s))), Xi)), "P", mz and mx)
    for side, (f, tgt, mono) in acts.items():
        I = prog[side] - outs[side]
        kept = sum(1 for s in I if key(vec(f(s))) in prog[tgt])
        outk = sum(1 for s in outs[side] if key(vec(f(s))) in outs[tgt])
        res.setdefault((side, e['slot'], bool(mono)), []).append((kept, outk))
print("side  slot      acts by signed permutations   elements   internal forms kept: best, mean   outputs onto outputs: min")
for (side, slot, mono), v in sorted(res.items()):
    k = [x[0] for x in v]
    print(f"  {side:3s} {slot:9s} {str(mono):28s} {len(v):6d}   {max(k):5d} of {len(prog[side] - outs[side]):3d}, {sum(k) / len(k):6.1f}      {min(x[1] for x in v):3d} of {len(outs[side])}")
