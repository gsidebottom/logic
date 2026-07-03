#!/usr/bin/env python3
"""Brent equations mod 2 for fast matrix-multiplication schemes.

A scheme for multiplying an n1 x n2 matrix A by an n2 x n3 matrix B with r
products is three bit tensors (over GF(2)):

    alpha[m][a][b]  -- coefficient of A[a,b] in product m
    beta[m][c][d]   -- coefficient of B[c,d] in product m
    gamma[m][p][q]  -- coefficient of product m in C[p,q]

    M_m = (sum_ab alpha[m][a][b] A[a,b]) * (sum_cd beta[m][c][d] B[c,d])
    C[p,q] = sum_m gamma[m][p][q] M_m

Correctness (mod 2) <=> the Brent equations: for all a,b,c,d,p,q

    XOR_m alpha[m][a][b] & beta[m][c][d] & gamma[m][p][q]
        = (b==c) & (a==p) & (d==q)

i.e. (n1*n2*n3)^2 cubic XOR equations over r*(n1*n2 + n2*n3 + n1*n3) vars.
For n=3, r=23: 729 equations (27 with RHS 1), 621 variables.

Usage:
  python3 matmul/brent.py selftest            # verify Strassen 2x2x2/7 + stats
  python3 matmul/brent.py cnf n1 n2 n3 r out.cnf   # DIMACS (Tseitin+XOR chain)
  python3 matmul/brent.py decode n1 n2 n3 r model.txt  # verify a kissat -v model
"""
import sys
import itertools
import random


# ---------------------------------------------------------------- equations

def var_counts(n1, n2, n3, r):
    na, nb, ng = r * n1 * n2, r * n2 * n3, r * n1 * n3
    return na, nb, ng


def brent_equations(n1, n2, n3, r):
    """Yield (monomials, rhs): monomials is a list of r (va, vb, vg) variable
    indices (0-based: alpha block, then beta, then gamma), rhs in {0,1}."""
    na, nb, _ = var_counts(n1, n2, n3, r)

    def a_idx(m, a, b):
        return m * n1 * n2 + a * n2 + b

    def b_idx(m, c, d):
        return na + m * n2 * n3 + c * n3 + d

    def g_idx(m, p, q):
        return na + nb + m * n1 * n3 + p * n3 + q

    eqs = []
    for a, b in itertools.product(range(n1), range(n2)):
        for c, d in itertools.product(range(n2), range(n3)):
            for p, q in itertools.product(range(n1), range(n3)):
                rhs = 1 if (b == c and a == p and d == q) else 0
                mons = [(a_idx(m, a, b), b_idx(m, c, d), g_idx(m, p, q))
                        for m in range(r)]
                eqs.append((mons, rhs))
    return eqs


def verify_bits(bits, n1, n2, n3, r, eqs=None):
    """bits: dict/list var-index -> 0/1. Returns #violated equations."""
    if eqs is None:
        eqs = brent_equations(n1, n2, n3, r)
    bad = 0
    for mons, rhs in eqs:
        acc = 0
        for va, vb, vg in mons:
            acc ^= bits[va] & bits[vb] & bits[vg]
        bad += (acc != rhs)
    return bad


def scheme_to_bits(alpha, beta, gamma, n1, n2, n3, r):
    """alpha[m][(a,b)]... given as sets of index pairs per product (0-based)."""
    na, nb, ng = var_counts(n1, n2, n3, r)
    bits = [0] * (na + nb + ng)
    for m in range(r):
        for (a, b) in alpha[m]:
            bits[m * n1 * n2 + a * n2 + b] = 1
        for (c, d) in beta[m]:
            bits[na + m * n2 * n3 + c * n3 + d] = 1
        for (p, q) in gamma[m]:
            bits[na + nb + m * n1 * n3 + p * n3 + q] = 1
    return bits


# ---------------------------------------------------------------- schemes

def strassen():
    """Strassen 2x2x2, 7 products (0-indexed pairs), mod-2 (signs dropped)."""
    A = [
        [(0, 0), (1, 1)],          # M1 = (A11+A22)(B11+B22)
        [(1, 0), (1, 1)],          # M2 = (A21+A22) B11
        [(0, 0)],                  # M3 = A11 (B12-B22)
        [(1, 1)],                  # M4 = A22 (B21-B11)
        [(0, 0), (0, 1)],          # M5 = (A11+A12) B22
        [(1, 0), (0, 0)],          # M6 = (A21-A11)(B11+B12)
        [(0, 1), (1, 1)],          # M7 = (A12-A22)(B21+B22)
    ]
    B = [
        [(0, 0), (1, 1)],
        [(0, 0)],
        [(0, 1), (1, 1)],
        [(1, 0), (0, 0)],
        [(1, 1)],
        [(0, 0), (0, 1)],
        [(1, 0), (1, 1)],
    ]
    # C11=M1+M4-M5+M7  C12=M3+M5  C21=M2+M4  C22=M1-M2+M3+M6
    C = [
        [(0, 0), (1, 1)],          # M1 in C11, C22
        [(1, 0), (1, 1)],          # M2 in C21, C22
        [(0, 1), (1, 1)],          # M3 in C12, C22
        [(0, 0), (1, 0)],          # M4 in C11, C21
        [(0, 0), (0, 1)],          # M5 in C11, C12
        [(1, 1)],                  # M6 in C22
        [(0, 0)],                  # M7 in C11
    ]
    return A, B, C


def laderman():
    """Laderman 1976, 23 products, mod 2 (signs dropped). 0-indexed.
    Transcribed from Bull. AMS 82(1):126-128 (symbolically verified over Z)."""
    A = [
        [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 1), (2, 2)],  # m1
        [(0, 0), (1, 0)],                                          # m2
        [(1, 1)],                                                  # m3
        [(0, 0), (1, 0), (1, 1)],                                  # m4
        [(1, 0), (1, 1)],                                          # m5
        [(0, 0)],                                                  # m6
        [(0, 0), (2, 0), (2, 1)],                                  # m7
        [(0, 0), (2, 0)],                                          # m8
        [(2, 0), (2, 1)],                                          # m9
        [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 0), (2, 1)],  # m10
        [(2, 1)],                                                  # m11
        [(0, 2), (2, 1), (2, 2)],                                  # m12
        [(0, 2), (2, 2)],                                          # m13
        [(0, 2)],                                                  # m14
        [(2, 1), (2, 2)],                                          # m15
        [(0, 2), (1, 1), (1, 2)],                                  # m16
        [(0, 2), (1, 2)],                                          # m17
        [(1, 1), (1, 2)],                                          # m18
        [(0, 1)],                                                  # m19
        [(1, 2)],                                                  # m20
        [(1, 0)],                                                  # m21
        [(2, 0)],                                                  # m22
        [(2, 2)],                                                  # m23
    ]
    B = [
        [(1, 1)],
        [(0, 1), (1, 1)],
        [(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 2)],
        [(0, 0), (0, 1), (1, 1)],
        [(0, 0), (0, 1)],
        [(0, 0)],
        [(0, 0), (0, 2), (1, 2)],
        [(0, 2), (1, 2)],
        [(0, 0), (0, 2)],
        [(1, 2)],
        [(0, 0), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1)],
        [(1, 1), (2, 0), (2, 1)],
        [(1, 1), (2, 1)],
        [(2, 0)],
        [(2, 0), (2, 1)],
        [(1, 2), (2, 0), (2, 2)],
        [(1, 2), (2, 2)],
        [(2, 0), (2, 2)],
        [(1, 0)],
        [(2, 1)],
        [(0, 2)],
        [(0, 1)],
        [(2, 2)],
    ]
    csets = {
        (0, 0): [6, 14, 19], (0, 1): [1, 4, 5, 6, 12, 14, 15],
        (0, 2): [6, 7, 9, 10, 14, 16, 18], (1, 0): [2, 3, 4, 6, 14, 16, 17],
        (1, 1): [2, 4, 5, 6, 20], (1, 2): [14, 16, 17, 18, 21],
        (2, 0): [6, 7, 8, 11, 12, 13, 14], (2, 1): [12, 13, 14, 15, 22],
        (2, 2): [6, 7, 8, 9, 23],
    }
    C = [[] for _ in range(23)]
    for (p, q), ms in csets.items():
        for m in ms:
            C[m - 1].append((p, q))
    return A, B, C


# ---------------------------------------------------------------- CNF

def to_cnf(n1, n2, n3, r):
    """Tseitin: aux var per monomial (AND3), XOR chain per equation.
    Returns (nvars, clauses). Real vars are 1..na+nb+ng (DIMACS 1-based)."""
    na, nb, ng = var_counts(n1, n2, n3, r)
    nreal = na + nb + ng
    eqs = brent_equations(n1, n2, n3, r)
    clauses = []
    nxt = nreal + 1

    def and3(x, y, z):
        nonlocal nxt
        t = nxt
        nxt += 1
        clauses.extend([[-t, x], [-t, y], [-t, z], [t, -x, -y, -z]])
        return t

    def xor2(u, v):
        nonlocal nxt
        t = nxt
        nxt += 1
        clauses.extend([[-t, u, v], [-t, -u, -v], [t, -u, v], [t, u, -v]])
        return t

    for mons, rhs in eqs:
        ps = [and3(va + 1, vb + 1, vg + 1) for va, vb, vg in mons]
        t = ps[0]
        for p in ps[1:]:
            t = xor2(t, p)
        clauses.append([t if rhs else -t])
    return nxt - 1, clauses


def write_dimacs(path, nvars, clauses):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")


def decode_model(path, n1, n2, n3, r):
    """Parse 'v ...' lines (kissat/cadical), verify the real-var prefix."""
    lits = []
    for line in open(path):
        if line.startswith("v"):
            lits += [int(x) for x in line.split()[1:] if x != "0"]
    nreal = sum(var_counts(n1, n2, n3, r))
    bits = [0] * nreal
    for l in lits:
        if 1 <= abs(l) <= nreal:
            bits[abs(l) - 1] = 1 if l > 0 else 0
    bad = verify_bits(bits, n1, n2, n3, r)
    print(f"decoded scheme: {bad} violated Brent equations "
          f"({'VALID SCHEME' if bad == 0 else 'INVALID'})")
    if bad == 0:
        na, nb, _ = var_counts(n1, n2, n3, r)
        for m in range(r):
            al = [f"A{a+1}{b+1}" for a in range(n1) for b in range(n2)
                  if bits[m * n1 * n2 + a * n2 + b]]
            be = [f"B{c+1}{d+1}" for c in range(n2) for d in range(n3)
                  if bits[na + m * n2 * n3 + c * n3 + d]]
            print(f"  M{m+1:2d} = ({'+'.join(al) or '0'})*({'+'.join(be) or '0'})")
        for p in range(n1):
            for q in range(n3):
                ms = [f"M{m+1}" for m in range(r)
                      if bits[na + nb + m * n1 * n3 + p * n3 + q]]
                print(f"  C{p+1}{q+1} = {'+'.join(ms) or '0'}")
    return bad


# ---------------------------------------------------------------- main

def selftest():
    # Strassen verifies exactly
    A, B, C = strassen()
    bits = scheme_to_bits(A, B, C, 2, 2, 2, 7)
    eqs = brent_equations(2, 2, 2, 7)
    bad = verify_bits(bits, 2, 2, 2, 7, eqs)
    print(f"strassen 2x2x2 r=7: {bad}/{len(eqs)} violated "
          f"({'OK' if bad == 0 else 'FAIL'})")
    assert bad == 0

    # Laderman verifies exactly
    A, B, C = laderman()
    lbits = scheme_to_bits(A, B, C, 3, 3, 3, 23)
    lbad = verify_bits(lbits, 3, 3, 3, 23)
    print(f"laderman 3x3x3 r=23: {lbad}/729 violated "
          f"({'OK' if lbad == 0 else 'FAIL'}), support={sum(lbits)}/621")
    assert lbad == 0

    # sensitivity: single bit flips break it; random is ~half wrong
    rng = random.Random(0)
    flips_bad = 0
    for _ in range(20):
        i = rng.randrange(len(bits))
        bits[i] ^= 1
        flips_bad += (verify_bits(bits, 2, 2, 2, 7, eqs) > 0)
        bits[i] ^= 1
    print(f"single-bit-flip breaks scheme: {flips_bad}/20")
    rnd = [rng.randint(0, 1) for _ in bits]
    print(f"random assignment violates: {verify_bits(rnd, 2, 2, 2, 7, eqs)}"
          f"/{len(eqs)}")

    # instance stats
    for (x, y, z, r) in [(2, 2, 2, 7), (2, 2, 2, 6), (3, 3, 3, 23),
                         (3, 3, 3, 22)]:
        eqs = brent_equations(x, y, z, r)
        nv = sum(var_counts(x, y, z, r))
        odd = sum(rhs for _, rhs in eqs)
        cv, cc = to_cnf(x, y, z, r)
        print(f"{x}x{y}x{z} r={r}: {nv} vars, {len(eqs)} eqs ({odd} odd) "
              f"| CNF: {cv} vars, {len(cc)} clauses")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    if cmd == "selftest":
        selftest()
    elif cmd == "cnf":
        n1, n2, n3, r = map(int, sys.argv[2:6])
        nv, cls = to_cnf(n1, n2, n3, r)
        rest = sys.argv[7:]
        if "--fix-scheme" in rest:
            name = rest[rest.index("--fix-scheme") + 1]
            nfix = int(rest[rest.index("--nfix") + 1])
            seed = int(rest[rest.index("--seed") + 1]) if "--seed" in rest \
                else 1
            sch = {"laderman": laderman, "strassen": strassen}[name]()
            bits = scheme_to_bits(*sch, n1, n2, n3, r)
            rng = random.Random(seed)
            for v in rng.sample(range(len(bits)), nfix):
                cls.append([v + 1 if bits[v] else -(v + 1)])
            print(f"fixed {nfix} base vars from {name} (seed {seed})")
        write_dimacs(sys.argv[6], nv, cls)
        print(f"wrote {sys.argv[6]}: {nv} vars, {len(cls)} clauses")
    elif cmd == "decode":
        n1, n2, n3, r = map(int, sys.argv[2:6])
        sys.exit(1 if decode_model(sys.argv[6], n1, n2, n3, r) else 0)
    else:
        sys.exit(f"unknown cmd {cmd}")
