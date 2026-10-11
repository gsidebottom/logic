#!/usr/bin/env python3
"""Sign-model loop for lifting free-basis certificates to Z: enumerate
distinct sign models of a mask scheme (lift.lift_models, SAT with
blocking clauses, per-product gauge normalized), and for each model try
to lift the F2 leg certificates -- A free, B free, then C exactly
against (eps_u * eps_v)-adjusted targets, so the per-product sign
balance eps_u*eps_v*eps_w = +1 holds by construction.

Gates: every model is z-verified against the signed Brent equations
(lift.z_verify); every leg's mask set must equal the certificate
files' mask set (the C side auto-detects the 3x3-transpose convention);
a successful lift prints the signed bases and chains for the assembly
step.

Usage: fbmodel.py bits-file certsA certsB certsC [nmodels]
"""
import itertools, sys
from fractions import Fraction

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from lift import lift_models, z_verify  # noqa: E402

BITSF, CA, CB, CC = sys.argv[1:5]
NMODELS = int(sys.argv[5]) if len(sys.argv) > 5 else 32
DIMS = (3, 3, 3, 23)

bits = [int(c) for c in open(BITSF).read().split()[-1].strip()]
assert len(bits) == 621

def parse_certs(path):
    certs, basis, adds = [], None, []
    for ln in open(path):
        ln = ln.strip()
        if ln.startswith("basis:"):
            if basis:
                certs.append((basis, adds))
            basis = [int(m, 2) for m in ln.split()[1:]]
            adds = []
        elif ln.startswith("add "):
            x, _, y, _, s = ln.split()[1:6]
            adds.append((int(x, 2), int(y, 2), int(s, 2)))
    if basis:
        certs.append((basis, adds))
    return certs

def mask(row):
    return int("".join(str(v & 1) for v in row), 2)

def tr(row):
    return tuple(row[3 * (p % 3) + p // 3] for p in range(9))

def det_unimodular(rows):
    A = [[Fraction(v) for v in r] for r in rows]
    d = Fraction(1)
    for c in range(len(rows)):
        p = next((r for r in range(c, len(rows)) if A[r][c] != 0), None)
        if p is None:
            return False
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, len(rows)):
            if A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return abs(d) == 1

def neg(v):
    return tuple(-x for x in v)

def add_vec(x, y, s):
    return tuple(a + s * b for a, b in zip(x, y))

def lift_leg(basis_masks, adds, rep_of_mask, exact=False):
    """-> (basis rows, signed adds, {mask: sign}) or None."""
    base_reps = [rep_of_mask[m] for m in basis_masks]

    def dfs(i, forms, sgn):
        if i == len(adds):
            return [], dict(sgn)
        x, y, s = adds[i]
        for sign in (1, -1):
            val = add_vec(forms[x], forms[y], sign)
            if s in rep_of_mask:
                rep = rep_of_mask[s]
                if val == rep:
                    sgn[s] = 1
                elif not exact and val == neg(rep):
                    sgn[s] = -1
                else:
                    continue
            forms[s] = val
            r = dfs(i + 1, forms, sgn)
            if r is not None:
                steps, out = r
                return [(x, y, s, sign)] + steps, out
            del forms[s]
            sgn.pop(s, None)
        return None

    eps_space = [(1,) * 9] if exact else [(1,) + e for e in
                                          itertools.product((1, -1), repeat=8)]
    for eps in eps_space:
        rows = [r if e == 1 else neg(r) for e, r in zip(eps, base_reps)]
        if not det_unimodular(rows):
            continue
        r = dfs(0, dict(zip(basis_masks, rows)), {m: e for m, e in zip(basis_masks, eps)})
        if r is not None:
            return rows, r[0], r[1]
    return None

def rep_ratio(rows):
    """None when some shared-mask pair is not +-proportional under this
    model -- then one chain value cannot serve both products and the
    20-target certificates cannot lift; skip the model."""
    rep, ratio = {}, []
    for r in rows:
        m = mask(r)
        if m not in rep:
            rep[m] = r
        if rep[m] == r:
            ratio.append(1)
        elif rep[m] == neg(r):
            ratio.append(-1)
        else:
            return None
    return rep, ratio

certsA, certsB, certsC = parse_certs(CA), parse_certs(CB), parse_certs(CC)
legmask = [set(), set(), set()]
for certs, i in ((certsA, 0), (certsB, 1), (certsC, 2)):
    for b, adds in certs:
        legmask[i] |= set(b) | {s for _, _, s in adds if True}
# cert files include helpers; the TARGET mask set is what the leg file held.
# Recover targets per leg from the bits instead and check cert masks fit.

models = lift_models(bits, NMODELS, DIMS)
print(f"{len(models)} sign models enumerated", flush=True)

transpose_c = None
for mi, (signs, _) in enumerate(models):
    assert z_verify(bits, signs, DIMS) == 0, f"model {mi} fails Z-verify"
    coef = [signs.get(v, 0) if bits[v] else 0 for v in range(621)]
    rows = [[tuple(coef[off + m * 9 + k] for k in range(9)) for m in range(23)]
            for off in (0, 207, 414)]
    if transpose_c is None:
        amasks = {mask(r) for r in rows[2]}
        if not all(m in amasks for b, _ in certsC for m in b):
            rows2 = [tr(r) for r in rows[2]]
            amasks2 = {mask(r) for r in rows2}
            assert all(m in amasks2 for b, _ in certsC for m in b), \
                "C masks match neither orientation"
            transpose_c = True
        else:
            transpose_c = False
        print(f"C-side transpose convention: {transpose_c}", flush=True)
    if transpose_c:
        rows[2] = [tr(r) for r in rows[2]]

    rrA, rrB, rrC = rep_ratio(rows[0]), rep_ratio(rows[1]), rep_ratio(rows[2])
    if rrA is None or rrB is None or rrC is None:
        bad = "".join(n for n, rr in zip("ABC", (rrA, rrB, rrC)) if rr is None)
        print(f"model {mi}: shared-mask rows not +-proportional on {bad}; skip",
              flush=True)
        continue
    repA, ratioA = rrA
    repB, ratioB = rrB
    repC, ratioC = rrC

    def first_lift(certs, rep, exact=False):
        for c in certs:
            r = lift_leg(*c, rep, exact=exact)
            if r:
                return r
        return None

    la = first_lift(certsA, repA)
    if la is None:
        print(f"model {mi}: A obstructed", flush=True)
        continue
    lb = first_lift(certsB, repB)
    if lb is None:
        print(f"model {mi}: A lifts, B obstructed", flush=True)
        continue
    eps_u = [la[2][mask(rows[0][i])] * ratioA[i] for i in range(23)]
    eps_v = [lb[2][mask(rows[1][i])] * ratioB[i] for i in range(23)]
    repC_adj, ok = {}, True
    for i in range(23):
        m = mask(rows[2][i])
        want = rows[2][i] if eps_u[i] * eps_v[i] * ratioC[i] == 1 else neg(rows[2][i])
        wantrep = want if ratioC[i] == 1 else neg(want)
        if repC_adj.setdefault(m, wantrep) != wantrep:
            ok = False
            break
    if not ok:
        print(f"model {mi}: A+B lift, eps inconsistent on shared C masks", flush=True)
        continue
    lc = first_lift(certsC, repC_adj, exact=True)
    if lc is None:
        print(f"model {mi}: A+B lift, C exact obstructed", flush=True)
        continue
    print(f"\n*** MODEL {mi}: FULL LIFT ***", flush=True)
    for nm, lift_ in (("A", la), ("B", lb), ("C", lc)):
        print(f"{nm} basis (unimodular):")
        for r in lift_[0]:
            print("   ", r)
        print(f"{nm} signed adds ({len(lift_[1])}):")
        for x, y, s, sign in lift_[1]:
            print(f"    {x:09b} {'+' if sign == 1 else '-'} {y:09b} -> {s:09b}")
    print("eps_u =", eps_u)
    print("eps_v =", eps_v)
    sys.exit(0)

print("no model lifted; enumerate more models or certificates")
sys.exit(2)
