#!/usr/bin/env python3
"""Decisive cyclic 50 instance: the cyclic CNF (orbit-quotiented Brent
system) conjoined with "the A-leg's F2 free-basis cost is <= A".

A cyclic scheme's three legs coincide up to a coordinate permutation,
so its per-step cost is 3a + 14 with a the A-leg's exact free-basis
cost (over F2).  a <= 12 is therefore exactly per-step <= 50.

Leg cost <= A is encoded as an addition chain: forms F_0..F_8 are nine
free basis vectors (arbitrary nonzero 9-bit values, lexicographically
increasing -- reordering basis vectors is always possible), and
F_9..F_{8+A} are additions, each the XOR of two distinct earlier forms
(one-hot left/right selectors, left < right).  Every A-leg row must
equal some form.  The rows span F2^9 in any valid scheme, so coverage
forces the basis to be independent; no rank constraint is needed.
F2 is finite, so there is no free-vector scope caveat: SAT means a
cyclic scheme with F2 per-step <= 3A + 14 exists; UNSAT means none does
in this product-orbit ansatz.

Bit v of the scheme is CNF variable rep[v]+1 (the orbit map).  Add the
chain to the UNBROKEN quotient CNF; symmetry-break afterwards.

Usage: symshape.py base.cnf cyc3.map A out.cnf [--fix sol.bits]
  (--fix pins the 621 bits to a known solution: the encoder gate)
"""
import sys

base, mapf, A, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
fix = sys.argv[sys.argv.index("--fix") + 1] if "--fix" in sys.argv else None

lines = open(base).read().split("\n")
hdr = lines[0].split()
assert hdr[:2] == ["p", "cnf"]
nv = int(hdr[2])
clauses = [ln for ln in lines[1:] if ln.strip() and not ln.startswith("c")]

rep = {}
for ln in open(mapf):
    v, r = ln.split()
    rep[int(v)] = int(r)


def new():
    global nv
    nv += 1
    return nv


def add(*lits):
    clauses.append(" ".join(str(l) for l in lits) + " 0")


def exactly_one(xs):
    add(*xs)
    for i in range(len(xs)):
        for j in range(i + 1, len(xs)):
            add(-xs[i], -xs[j])


ROW = [[rep[m * 9 + k] + 1 for k in range(9)] for m in range(23)]
NF = 9 + A
F = [[new() for _ in range(9)] for _ in range(NF)]

# basis vectors: nonzero, strictly lex-increasing (bit 8 most significant)
for i in range(9):
    add(*F[i])


def lex_less(a, b, guard=None):
    """a < b as 9-bit numbers, bit 8 most significant; with `guard`,
    only required when the guard literal is false."""
    # prefix-equal chain from the top bit down
    eqp = None
    terms = []
    for k in range(8, -1, -1):
        lt = new()  # a_k = 0, b_k = 1, all higher bits equal
        add(-lt, -a[k])
        add(-lt, b[k])
        if eqp is not None:
            add(-lt, eqp)
        terms.append(lt)
        e = new()  # higher bits equal through bit k
        add(-e, -a[k], b[k])
        add(-e, a[k], -b[k])
        if eqp is not None:
            add(-e, eqp)
        eqp = e
    if guard is None:
        add(*terms)
    else:
        add(guard, *terms)


for i in range(8):
    lex_less(F[i], F[i + 1])

# additions: F_i = F_l XOR F_r, l < r < i
SEL = {}
for i in range(9, NF):
    L = [new() for _ in range(i)]
    R = [new() for _ in range(i)]
    SEL[i] = (L, R)
    exactly_one(L)
    exactly_one(R)
    for u in range(i):
        for w in range(u + 1):
            add(-L[u], -R[w])   # forbid r <= l
    for k in range(9):
        lb, rb = new(), new()
        for u in range(i):
            add(-L[u], -lb, F[u][k])
            add(-L[u], lb, -F[u][k])
            add(-R[u], -rb, F[u][k])
            add(-R[u], rb, -F[u][k])
        f = F[i][k]
        add(-f, lb, rb)
        add(-f, -lb, -rb)
        add(f, -lb, rb)
        add(f, lb, -rb)

# symmetry breaking (both sound for "cost <= A"):
# (a) all forms pairwise distinct -- a shorter chain can always be
#     padded with new distinct sums (the span is all of F2^9);
# (b) consecutive independent additions in increasing value order --
#     the greedy smallest-available topological order of any chain
#     satisfies it.
for i in range(NF):
    for j in range(max(i + 1, 9), NF):
        ds = []
        for k in range(9):
            d = new()
            add(-d, F[i][k], F[j][k])
            add(-d, -F[i][k], -F[j][k])
            ds.append(d)
        add(*ds)
for i in range(9, NF - 1):
    L1, R1 = SEL[i + 1]
    uses = new()            # addition i+1 uses form i
    add(-L1[i], uses)
    add(-R1[i], uses)
    add(-uses, L1[i], R1[i])
    lex_less(F[i], F[i + 1], guard=uses)

# coverage: every A-leg row equals some form
for m in range(23):
    cov = []
    for i in range(NF):
        c = new()
        for k in range(9):
            add(-c, -ROW[m][k], F[i][k])
            add(-c, ROW[m][k], -F[i][k])
        cov.append(c)
    add(*cov)

if fix:
    bits = open(fix).read().split()[-1].strip()
    assert len(bits) == 621
    for v in range(621):
        lit = rep[v] + 1
        add(lit if bits[v] == "1" else -lit)

with open(out, "w") as f:
    f.write(f"p cnf {nv} {len(clauses)}\n")
    f.write("\n".join(clauses) + "\n")
print(f"{out}: leg cost <= {A} (per-step <= {3 * A + 14}), {nv} vars, "
      f"{len(clauses)} clauses" + (f", pinned to {fix}" if fix else ""))
