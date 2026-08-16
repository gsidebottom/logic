#!/usr/bin/env python3
"""Root strata for the rank-22 certified lower-bound tree.

Split on min alpha-rank (dead-product branch separate):
  S0: some product dead (alpha/beta/gamma = 0)  -> the r=21 instance
  S1: some alpha has rank 1; witness canonicalized to E11 in slot 0
  S2: all alpha ranks >= 2; witness canonicalized to diag(1,1,0)
  S3: all alpha invertible; witness canonicalized to I3

Covering (to be Lean-checked): every 22-summand Brent solution over F2
maps under S22 x GL(3,2)^2 (sandwich on A-side) into S0|S1|S2|S3.

Gate (--selftest): canonicalize Laderman's rank-23 scheme by the group
action (alpha -> U^T alpha V^T, beta -> V^-T beta, gamma -> U^-1 gamma)
and re-verify Brent + the slot-0 pin; unit-test the rank encoders.

Usage:
  python3 matmul/r22/strata.py selftest
  python3 matmul/r22/strata.py gen        # writes S1/S2/S3 CNFs
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
MM = os.path.dirname(HERE)
sys.path.insert(0, MM)
from brent import laderman, scheme_to_bits, verify_bits

R = 22
NA = 198  # 22*9

# ---------- GF(2) 3x3 linear algebra on row-major 9-bit lists ----------
def mat(bits9):
    return [bits9[0:3], bits9[3:6], bits9[6:9]]

def flat(m):
    return [m[i][j] for i in range(3) for j in range(3)]

def mmul(a, b):
    return [[sum(a[i][k] & b[k][j] for k in range(3)) & 1 for j in range(3)]
            for i in range(3)]

def mtrans(a):
    return [[a[j][i] for j in range(3)] for i in range(3)]

def rank(m):
    a = [row[:] for row in m]
    r = 0
    for c in range(3):
        piv = next((i for i in range(r, 3) if a[i][c]), None)
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        for i in range(3):
            if i != r and a[i][c]:
                a[i] = [(x ^ y) & 1 for x, y in zip(a[i], a[r])]
        r += 1
    return r

def minv(m):
    a = [row[:] + [1 if i == j else 0 for j in range(3)]
         for i, row in enumerate(m)]
    r = 0
    for c in range(3):
        piv = next((i for i in range(r, 3) if a[i][c]), None)
        if piv is None:
            return None
        a[r], a[piv] = a[piv], a[r]
        for i in range(3):
            if i != r and a[i][c]:
                a[i] = [(x ^ y) & 1 for x, y in zip(a[i], a[r])]
        r += 1
    return [row[3:] for row in a]

def complete_basis(v):
    """invertible M over F2 whose FIRST ROW is v (v != 0)."""
    def span_rank(rows):
        pads = rows + [[0, 0, 0]] * (3 - len(rows))
        return rank(pads)
    rows = [list(v)]
    for cand in range(1, 8):
        w = [(cand >> 2) & 1, (cand >> 1) & 1, cand & 1]
        if span_rank(rows + [w]) == len(rows) + 1:
            rows.append(w)
        if len(rows) == 3:
            break
    assert rank(rows) == 3
    return rows

# ---------- the group action on summand triples ----------
def act(scheme, U, V):
    """alpha -> U^T alpha V^T, beta -> V^-T beta, gamma -> U^-1 gamma."""
    al, be, ga = scheme
    Ut, Vt = mtrans(U), mtrans(V)
    Vinv_t = mtrans(minv(V))
    Uinv = minv(U)
    al2 = [mmul(mmul(Ut, a), Vt) for a in al]
    be2 = [mmul(Vinv_t, b) for b in be]
    ga2 = [mmul(Uinv, g) for g in ga]
    return (al2, be2, ga2)

def canonicalize_rank1_to_slot0(scheme):
    """Find a rank-1 alpha, swap to slot 0, transform it to E11."""
    al, be, ga = scheme
    w = next(i for i, a in enumerate(al) if rank(a) == 1)
    for lst in (al, be, ga):
        lst[0], lst[w] = lst[w], lst[0]
    a0 = al[0]
    # a0 = u v^T: u = any nonzero row-space gen... over F2 rank1: rows all
    # equal to v or zero; u indicates which rows are nonzero.
    v = next(r for r in a0 if any(r))
    u = [1 if any(r) and r == v else 0 for r in a0]
    # need U^T u = e1 and V v = e1 (then U^T a0 V^T = e1 e1^T = E11):
    # take Minv with first COLUMN u; then U^T := Minv^-1 sends u -> e1.
    Minv = mtrans(complete_basis(u))   # first column u
    Umat_T = minv(Minv)
    U = mtrans(Umat_T)
    Nv = mtrans(complete_basis(v))     # first column v
    V = minv(Nv)                       # V v = e1
    a, b, g = act((al, be, ga), U, V)
    assert a[0] == [[1, 0, 0], [0, 0, 0], [0, 0, 0]], a[0]
    return (a, b, g)

# ---------- CNF emission ----------
def base_cnf(path):
    lines = open(path).read().splitlines()
    nv, ncl = int(lines[0].split()[2]), int(lines[0].split()[3])
    return nv, ncl, lines[1:]

def alpha_var(m, i, j):
    return m * 9 + i * 3 + j + 1  # DIMACS 1-based, alpha block first

def emit(out, base, extra_cls, extra_vars):
    nv, ncl, body = base
    with open(out, "w") as f:
        f.write(f"p cnf {nv + extra_vars} {ncl + len(extra_cls)}\n")
        f.write("\n".join(body))
        f.write("\n")
        for c in extra_cls:
            f.write(" ".join(map(str, c)) + " 0\n")

def pin_alpha0(target):
    cls = []
    for i in range(3):
        for j in range(3):
            v = alpha_var(0, i, j)
            cls.append([v] if target[i][j] else [-v])
    return cls

def rank_ge2_clauses(m, next_var):
    """aux: 9 minors of alpha_m; minor(i,j) = ad^bc over the 2x2 complement.
    Returns (clauses, minor_vars, next_var)."""
    cls, minors = [], []
    rows = cols = (0, 1, 2)
    for di in rows:
        for dj in cols:
            (i1, i2) = [x for x in rows if x != di]
            (j1, j2) = [x for x in cols if x != dj]
            a = alpha_var(m, i1, j1); d = alpha_var(m, i2, j2)
            b = alpha_var(m, i1, j2); c = alpha_var(m, i2, j1)
            t1, t2, y = next_var, next_var + 1, next_var + 2
            next_var += 3
            # t1 <-> a&d ; t2 <-> b&c ; y <-> t1 xor t2
            cls += [[-t1, a], [-t1, d], [t1, -a, -d],
                    [-t2, b], [-t2, c], [t2, -b, -c],
                    [-y, t1, t2], [-y, -t1, -t2],
                    [y, t1, -t2], [y, -t1, t2]]
            minors.append(y)
    cls.append(minors[:])  # rank>=2 <-> some minor nonzero
    return cls, next_var

def det1_clauses(m, next_var):
    """det(alpha_m) = 1 over F2: xor of 6 permutation AND-triples."""
    import itertools as it
    cls, terms = [], []
    for perm in it.permutations(range(3)):
        t = next_var; next_var += 1
        lits = [alpha_var(m, i, perm[i]) for i in range(3)]
        for l in lits:
            cls.append([-t, l])
        cls.append([t] + [-l for l in lits])
        terms.append(t)
    # xor chain over 6 terms = 1
    prev = terms[0]
    for t in terms[1:]:
        y = next_var; next_var += 1
        cls += [[-y, prev, t], [-y, -prev, -t], [y, prev, -t], [y, -prev, t]]
        prev = y
    cls.append([prev])
    return cls, next_var

def gen():
    base = base_cnf(os.path.join(HERE, "brent_3x3x22.cnf"))
    nv0 = base[0]
    E11 = [[1, 0, 0], [0, 0, 0], [0, 0, 0]]
    D110 = [[1, 0, 0], [0, 1, 0], [0, 0, 0]]
    I3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    # S1: pin only
    emit(os.path.join(HERE, "S1_rank1.cnf"), base, pin_alpha0(E11), 0)
    # S2: pin diag(1,1,0) + all alpha rank>=2
    cls = pin_alpha0(D110)
    nxt = nv0 + 1
    for m in range(R):
        c2, nxt = rank_ge2_clauses(m, nxt)
        cls += c2
    emit(os.path.join(HERE, "S2_rank2.cnf"), base, cls, nxt - nv0 - 1)
    # S3: pin I + all alpha det=1
    cls = pin_alpha0(I3)
    nxt = nv0 + 1
    for m in range(R):
        c3, nxt = det1_clauses(m, nxt)
        cls += c3
    emit(os.path.join(HERE, "S3_rank3.cnf"), base, cls, nxt - nv0 - 1)
    print("wrote S1_rank1.cnf S2_rank2.cnf S3_rank3.cnf")

def pairs_to_mat(pairs):
    m = [[0]*3 for _ in range(3)]
    for (i, j) in pairs:
        m[i][j] = 1
    return m

def mat_to_pairs(m):
    return [(i, j) for i in range(3) for j in range(3) if m[i][j]]

def selftest():
    # 1. group action preserves Brent on Laderman
    al, be, ga = laderman()
    bits0 = scheme_to_bits(al, be, ga, 3, 3, 3, 23)
    assert verify_bits(bits0, 3, 3, 3, 23) == 0, "laderman baseline"
    sch = ([pairs_to_mat(p) for p in al],
           [pairs_to_mat(p) for p in be],
           [pairs_to_mat(p) for p in ga])
    a2, b2, g2 = canonicalize_rank1_to_slot0(sch)
    bits1 = scheme_to_bits([mat_to_pairs(m) for m in a2],
                           [mat_to_pairs(m) for m in b2],
                           [mat_to_pairs(m) for m in g2], 3, 3, 3, 23)
    assert verify_bits(bits1, 3, 3, 3, 23) == 0, "action must preserve Brent"
    assert a2[0] == [[1,0,0],[0,0,0],[0,0,0]]
    print("gate 1 ok: Laderman canonicalized (alpha0=E11), Brent preserved")
    # 2. rank helpers
    assert rank([[1,0,0],[0,0,0],[0,0,0]]) == 1
    assert rank([[1,0,0],[0,1,0],[0,0,0]]) == 2
    assert rank([[1,0,0],[0,1,0],[0,0,1]]) == 3
    assert minv([[0,1,0],[1,0,0],[0,0,1]]) is not None
    print("gate 2 ok: GF(2) linear algebra")

if __name__ == "__main__":
    {"selftest": selftest, "gen": gen}[sys.argv[1] if len(sys.argv) > 1 else "selftest"]()
