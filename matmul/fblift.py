#!/usr/bin/env python3
"""Sign-lift fbmin's F2 free-basis certificates to Z (any ring,
non-commutative): keep each chain DAG, replace every XOR by + or -,
lift the 9 basis forms to signed vectors, and require every
target-producing step to equal a signed scheme row -- Nielsen's
sec:lifting move (arXiv 2609.06588), done exactly by DFS.

Scheme rows come signed from the DB .tab (the same file the F2 legs
were reduced from).  Per product i the three legs may each pick a sign
eps, but a bilinear scheme only tolerates eps_u*eps_v*eps_w = +1
(negating two of a product's three factors is invisible).  So:

  1. lift the A leg freely  -> eps_u[i] per product;
  2. lift the B leg freely  -> eps_v[i];
  3. lift the C leg EXACTLY against targets (eps_u[i]*eps_v[i])*row_i,
     which forces eps_w = eps_u*eps_v, i.e. balance holds by
     construction.  In exact mode the basis signs are forced too, so
     only the unimodularity of the forced basis remains to check.

Every lifted basis must be unimodular over Z (det +-1): the uncounted
basis changes are then integer-invertible, giving the Karstadt-Schwartz
hoisting argument over every ring.  If a leg admits no lift under its
certificate, fbmin has other certificates (different bases/chains at
the same count); enumerate further solutions before concluding anything.

Usage: fblift.py schemes.tgz certA certB certC
"""
import itertools, sys, tarfile
from fractions import Fraction

TAB = "schemes/18x2+51x+4y6+6y4+13y3+z32+z28+z27/i19w225c4efh-000.tab"

def parse_tab(text):
    out, cur = [], []
    for ln in text.splitlines():
        if "|" not in ln:
            continue
        parts = [p.split() for p in ln.split("|")]
        if len(parts) != 3 or any(len(g) != 3 for g in parts):
            continue
        cur.append([[int(v) for v in g] for g in parts])
        if len(cur) == 3:
            out.append(tuple(tuple(v for r in cur for v in r[s]) for s in range(3)))
            cur = []
    return out

def mask(row):
    return int("".join(str(v & 1) for v in row), 2)

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
    assert certs, path
    return certs

def det_unimodular(rows):
    A = [[Fraction(v) for v in r] for r in rows]
    d = Fraction(1)
    n = len(rows)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return False
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            if A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return abs(d) == 1

def neg(v):
    return tuple(-x for x in v)

def add_vec(x, y, s):
    return tuple(a + s * b for a, b in zip(x, y))

def lift_leg(basis_masks, adds, rep_of_mask, name, exact=False):
    """DFS over basis signs and per-add signs.  rep_of_mask maps each
    target mask to a signed representative vector.  Free mode: a chain
    value matching +-rep is accepted, the sign recorded.  Exact mode:
    only +rep is accepted (targets already carry their required signs),
    and the basis signs are forced to +1.
    Returns (signed basis rows, signed adds, {mask: sign}) or None."""
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
    n_uni = n_dfs = 0
    for eps in eps_space:
        rows = [r if e == 1 else neg(r) for e, r in zip(eps, base_reps)]
        if not det_unimodular(rows):
            continue
        n_uni += 1
        forms = dict(zip(basis_masks, rows))
        sgn = {m: e for m, e in zip(basis_masks, eps)}
        r = dfs(0, forms, sgn)
        n_dfs += 1
        if r is not None:
            steps, out = r
            print(f"{name}: LIFTED ({len(steps)} signed adds, basis unimodular)")
            return rows, steps, out
    print(f"{name}: NO LIFT ({n_uni}/{len(eps_space)} basis signings unimodular, "
          f"{n_dfs} DFS runs all sign-obstructed)")
    return None

def load_scheme(tgz, tab=TAB):
    sm = parse_tab(tarfile.open(tgz, "r:gz").extractfile(tab).read().decode())
    assert len(sm) == 23
    return sm

def side_info(sm, side):
    rep, ratio = {}, []
    for a in sm:
        r = a[side]
        m = mask(r)
        if m not in rep:
            rep[m] = r
        if r == rep[m]:
            ratio.append(1)
        elif r == neg(rep[m]):
            ratio.append(-1)
        else:
            raise AssertionError("shared mask, rows not +-proportional")
    return rep, ratio

if __name__ != "__main__":
    pass
elif len(sys.argv) == 4 and sys.argv[2] in "ABC":
    sm = load_scheme(sys.argv[1])
    rep, _ = side_info(sm, "ABC".index(sys.argv[2]))
    certs = parse_certs(sys.argv[3])
    nlift = sum(1 for i, c in enumerate(certs)
                if lift_leg(*c, rep, f"{sys.argv[2]} cert {i}"))
    print(f"probe: {nlift}/{len(certs)} {sys.argv[2]}-leg certificates lift (free mode)")
    sys.exit(0)
else:
    TGZ, CERTA, CERTB, CERTC = sys.argv[1:5]
    sm = load_scheme(TGZ)

repA, ratioA = side_info(sm, 0)
repB, ratioB = side_info(sm, 1)
repC, ratioC = side_info(sm, 2)

certsA = parse_certs(CERTA)
certsB = parse_certs(CERTB)
certsC = parse_certs(CERTC)
print(f"certificates: A {len(certsA)}, B {len(certsB)}, C {len(certsC)}")

solution = None
for ia, ca in enumerate(certsA):
    la = lift_leg(*ca, repA, f"A cert {ia}")
    if not la:
        continue
    eps_u = [la[2][mask(sm[i][0])] * ratioA[i] for i in range(23)]
    for ib, cb in enumerate(certsB):
        lb = lift_leg(*cb, repB, f"B cert {ib}")
        if not lb:
            continue
        eps_v = [lb[2][mask(sm[i][1])] * ratioB[i] for i in range(23)]
        repC_adj, ok = {}, True
        for i in range(23):
            m = mask(sm[i][2])
            want = sm[i][2] if eps_u[i] * eps_v[i] == 1 else neg(sm[i][2])
            if repC_adj.setdefault(m, want) != want:
                ok = False  # shared C mask demands opposite signs
                break
        if not ok:
            continue
        for ic, cc in enumerate(certsC):
            lc = lift_leg(*cc, repC_adj, f"C cert {ic} (sign-balanced)", exact=True)
            if lc:
                solution = (ia, ib, ic, la, lb, lc, eps_u, eps_v)
                break
        if solution:
            break
    if solution:
        break

assert solution, "no (A,B,C) certificate combination lifts -- enumerate more"
ia, ib, ic, la, lb, lc, eps_u, eps_v = solution
print(f"\nSOLUTION: A cert {ia}, B cert {ib}, C cert {ic}")
print("SIGN BALANCE: eps_u*eps_v*eps_w = +1 for all 23 products by")
print("construction (C targets pre-multiplied by eps_u*eps_v).")
print("eps_u =", eps_u)
print("eps_v =", eps_v)
for nm, lift in (("A", la), ("B", lb), ("C", lc)):
    print(f"\n{nm} basis rows (signed, unimodular):")
    for r in lift[0]:
        print("   ", r)
    print(f"{nm} signed adds:")
    for x, y, s, sign in lift[1]:
        print(f"    {x:09b} {'+' if sign == 1 else '-'} {y:09b} -> {s:09b}")
print("\nLIFT COMPLETE: three signed chains from unimodular signed bases")
print("reproduce the signed scheme rows over Z => per-step 13+13+(12+14)")
print("= 52 holds over every ring (non-commutative included), pending the")
print("assembled end-to-end check (word-ring / Lean) as the final gate.")
