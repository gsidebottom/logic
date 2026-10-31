#!/usr/bin/env python3
"""Does the 89-operation P program of lam01c0_201 respect the point's stabilizer (RFC 2610, Section 4)?

An element g of the stabilizer permutes the 48 products with scalars: A P = P M, M monomial.  Feeding M p
to a program for P therefore computes A times its outputs, so a form s of the program goes to s M, and a
form f of a program for P^T goes to A f (columns of P go to columns of P).  Each program is a set of
linear forms up to scale; the test counts how many of its internal forms land on forms of the same
program.  Exact over Q.

Gates: each program computes its matrix; A P = P M holds for every element.
Positive control: at the 203 point L and R are stated to be one program up to relabelling, so some
element carrying R onto L must send R's forms onto L's.  Baseline: random signed permutations.

  symtest.py DIR203 [SAMPLES]     (DIR203 holds 4x4x4_48_203_{L,R,P}.{sms,slp})
"""
import os, random, sys
from collections import Counter
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE)
import stabilizer48 as ST
LT, F, C = ST.LT, ST.F, ST.C
d203 = sys.argv[1]; SAMPLES = int(sys.argv[2]) if len(sys.argv) > 2 else 200
rng = random.Random(1)
def forms(path, n):
    env = {f"i{k}": {k: Fr(1)} for k in range(n)}; out = {}
    for lhs, rhs in C.parse(open(path).read()):
        v, _ = C.linear(rhs, env); env[lhs] = v; out[lhs] = [v.get(k, Fr(0)) for k in range(n)]
    return out
def key(v):
    f = next((x for x in v if x), None); return None if f is None else tuple(x / f for x in v)
def sms(path):
    rows = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    r, c = int(rows[0][0]), int(rows[0][1]); M = [[Fr(0)] * c for _ in range(r)]
    for t in rows[1:]:
        if len(t) == 3 and t[0] != '0': M[int(t[0]) - 1][int(t[1]) - 1] = Fr(t[2])
    return M
def elements(prefix, names):
    U, V, W = F.read_lrp(prefix); Tg = (U, V, [LT.T(M) for M in W]); vcT, pcT = LT.colors(Tg); out = []
    for name, S in LT.s3_variants(Tg):
        if name not in names: continue
        vcS, pcS = LT.colors(S)
        for pi in LT.isomorphisms(vcS, pcS, vcT, pcT):
            g = LT.try_transport(S, Tg, pi)
            if g is not None: out.append((name, [pi[k] for k in range(48)], g))
    return Tg, out
mm, T = LT.mm, LT.T
def rs(v): return [v[i * 4:i * 4 + 4] for i in range(4)]
def vec(M): return [x for r in M for x in r]
def cyc(pi): return tuple(sorted(Counter(ST.cycle_type(pi)).items(), reverse=True))
def rand_like(pi):
    lab = list(range(48)); rng.shuffle(lab); q = [0] * 48
    for k in range(48): q[lab[k]] = lab[pi[k]]
    return q, [rng.choice((1, -1)) for _ in range(48)]
pre = os.path.join(HERE, "cand48/lam01c0_201")
P = sms(pre + "_P.sms"); Pc = [list(c) for c in zip(*P)]
fP = forms(pre + "_P.slp", 48); fT = forms(pre + "_Pt.slp", 16)
assert all(fP[f"o{j}"] == P[j] for j in range(16)), "P program does not compute P"
assert all(fT[f"o{k}"] == Pc[k] for k in range(48)), "P^T program does not compute P^T"
outP = {key(r) for r in P}; outT = {key(c) for c in Pc}
SP = {key(v) for v in fP.values()} - {None}; ST_ = {key(v) for v in fT.values()} - {None}
units = lambda n: {key([Fr(i == j) for j in range(n)]) for i in range(n)}
intP = SP - outP - units(48); intT = ST_ - outT - units(16)
print(f"P program: {len(SP)} distinct forms, {len(intP)} internal, {len(SP & outP)} outputs; P^T program: {len(ST_)} distinct forms, {len(intT)} internal")
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "verify_note.py")).read()
exec(src[src.index('pi = {"pi2"'):src.index('print("   pi are fixed')])
printed = {n: {a - 1: b - 1 for x, y in p for a, b in ((x, y), (y, x))} for n, p in pi.items()}
Tg, els = elements(pre, {"id", "cyc2+rev"})
print(f"stabilizer of lam01c0_201 keeping the P slot: {len(els)} elements")
rows = []
for name, pi_, g in els:
    X, Y, Z, Xi, Yi, Zi, a, b = g
    c = [a[k] * b[k] for k in range(48)]
    def act(C_):                                    # the file's C (P column reshaped) -> its image
        W = T(C_); im = mm(mm(Z, W if name == "id" else T(W)), Xi); return T(im)
    A = [list(col) for col in zip(*[vec(act(rs([Fr(i == j) for j in range(16)]))) for i in range(16)])]
    for k in range(48):                             # gate: A P = P M
        assert [sum(A[i][j] * Pc[k][j] for j in range(16)) for i in range(16)] == [c[k] * x for x in Pc[pi_[k]]], "A P != P M"
    img = lambda v: [v[pi_[k]] * c[k] for k in range(48)]
    fixedout = sum(1 for r in P if key(img(r)) in outP)
    ovP = sum(1 for s in intP if key(img(list(s))) in SP)
    ovT = sum(1 for f in intT if key([sum(A[i][j] * f[j] for j in range(16)) for i in range(16)]) in ST_)
    label = next((n for n, q in printed.items() if name == "id" and all(pi_[i] == q[i] for i in range(48))), "")
    identity = name == "id" and pi_ == list(range(48))
    rows.append((name, ST.order_of(ST.cycle_type(pi_)), cyc(pi_), fixedout, ovP, ovT, label, identity))
print("element                 outputs onto outputs  P internal forms kept  P^T internal forms kept")
for r in sorted(rows, key=lambda r: (not r[6], -r[4] - r[5])):
    if r[6]: print(f"  {r[6]:5s} (his Klein group)  {r[3]:3d} of 16            {r[4]:3d} of {len(intP)}              {r[5]:3d} of {len(intT)}")
rest = [r for r in rows if not r[7]]
print(f"all {len(rest)} non-identity elements: best P {max(r[4] for r in rest)}/{len(intP)}, best P^T {max(r[5] for r in rest)}/{len(intT)}; outputs onto outputs at most {max(r[3] for r in rest)}/16")
print("  by slot map and order, best (P, P^T):", sorted({(r[0], r[1], max(q[4] for q in rest if q[:2] == r[:2]), max(q[5] for q in rest if q[:2] == r[:2]), sum(1 for q in rest if q[:2] == r[:2])) for r in rest}))
bp = []; bt = []
pools = list({r[2]: e for r, e in zip(rows, els)}.values())
for s in range(SAMPLES):
    q, sg = rand_like(pools[s % len(pools)][1])
    bp.append(sum(1 for v in intP if key([v[q[k]] * sg[k] for k in range(48)]) in SP))
    p16 = list(range(16)); rng.shuffle(p16); sg16 = [rng.choice((1, -1)) for _ in range(16)]
    bt.append(sum(1 for f in intT if key([f[p16[i]] * sg16[i] for i in range(16)]) in ST_))
print(f"baseline, {SAMPLES} random signed permutations: P mean {sum(bp) / len(bp):.2f} max {max(bp)}; P^T mean {sum(bt) / len(bt):.2f} max {max(bt)}")
def control(prefix, label):
    fL = forms(prefix + "_L.slp", 16); fR = forms(prefix + "_R.slp", 16)
    SL = {key(v) for v in fL.values()} - {None} - units(16); SR = {key(v) for v in fR.values()} - {None} - units(16)
    _, es = elements(prefix, {"cyc2+rev"}); best = 0
    for name, pi_, g in es:
        X, Y = g[0], g[1]; Yi = g[4]
        best = max(best, sum(1 for s in SR if key(vec(mm(mm(X, T(rs(list(s)))), Yi))) in SL))
    rb = []
    for _ in range(SAMPLES):
        p16 = list(range(16)); rng.shuffle(p16); sg16 = [rng.choice((1, -1)) for _ in range(16)]
        rb.append(sum(1 for s in SR if key([s[p16[i]] * sg16[i] for i in range(16)]) in SL))
    print(f"{label}: {len(SR)} forms of R, {len(SL)} of L, {len(es)} elements carrying R onto L; best overlap {best}/{len(SR)}; random signed permutations max {max(rb)}")
print("== positive control: R's program onto L's ==")
control(os.path.join(d203, "4x4x4_48_203"), "203 point (should be nearly all)")
control(pre, "lam01c0_201 (our two programs)")
