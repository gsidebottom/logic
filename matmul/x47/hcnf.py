#!/usr/bin/env python3
"""Sandwich-group quotient of the Brent system for <4,4,4> schemes over F2, as CNF (the symmetry-prescribed
search of 2026-11-09, after Burichenko and Ballard-Ikenmeyer-Landsberg-Ryder for 3x3).
A group H of permutation triples g = (x, y, z) (each a permutation of 0..3, as the tuple p with the 1 of row i of
the matrix in column p[i]) acts on a product (U, V, W) (product m = <U_m,A><V_m,B>, C = sum_m product_m W_m) by
    U'[i][j] = U[x[i]][y[j]],   V'[i][j] = V[y[i]][z[j]],   W'[i][j] = W[x[i]][z[j]]
(the isotropy A -> X A Y^T, B -> Y B Z^T of the tensor).  A scheme is H-invariant when its set of products is.
A shape lists orbit types: for each subgroup K of H (the stabilizer of the representative) a count of orbits of
size |H|/|K|; the representative's 48 entries are the free variables, identified under K (U = k.U for k in K), and
the orbit's other products are the images under coset representatives.  Brent equations are rewritten in the free
variables (matmul/brent.py order), reduced mod 2 and deduplicated; one Tseitin AND per monomial, XOR ladders.
Groups: --group d8   the mod-2 image of the dihedral group of signed permutations in Stab(accurate_262)
        --group c4   its cyclic subgroup of order 4;   --group z2  its centre (order 2)
Usage: hcnf.py --group G --shape k0:c0,k1:c1,... [--lex] out.cnf   (k = subgroup index from `hcnf.py --group G --list`;
       --lex adds lex-leader symmetry breaking for the orbit swaps and the normalizer cosets, see symmetry_generators)
       hcnf.py --group G --list
       hcnf.py --group G --shape ... decode SOLVER_OUTPUT out.bits
"""
import sys, pathlib, itertools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))  # matmul/
from brent import brent_equations  # noqa: E402

N = 4
D8 = [((0,1,2,3),(0,1,2,3),(0,1,2,3)), ((0,1,3,2),(1,0,3,2),(0,1,3,2)), ((1,0,2,3),(2,3,0,1),(1,0,2,3)),
      ((1,0,3,2),(3,2,1,0),(1,0,3,2)), ((2,3,0,1),(3,1,2,0),(2,3,0,1)), ((2,3,1,0),(1,3,0,2),(2,3,1,0)),
      ((3,2,0,1),(2,0,3,1),(3,2,0,1)), ((3,2,1,0),(0,2,1,3),(3,2,1,0))]
def comp(p, q): return tuple(p[q[i]] for i in range(N))          # (p o q)[i] = p[q[i]]
def gcomp(g, h): return tuple(comp(g[k], h[k]) for k in range(3))
def closure(gens):
    G = {tuple((0,1,2,3) for _ in range(3))} | set(gens); changed = True
    while changed:
        changed = False
        for a in list(G):
            for b in list(G):
                c = gcomp(a, b)
                if c not in G: G.add(c); changed = True
    return sorted(G)
GROUPS = {"d8": D8, "c4": closure([D8[5]]), "z2": closure([D8[3]])}
def subgroups(G):
    Gs = set(G); subs = set()
    for r in range(0, 4):
        for gens in itertools.combinations(G, r):
            K = closure(gens)
            if set(K) <= Gs: subs.add(tuple(K))
    subs = sorted(subs, key=lambda K: (len(K), K))
    return subs
def act(g, U, V, W):
    x, y, z = g
    return ([[U[x[i]][y[j]] for j in range(N)] for i in range(N)],
            [[V[y[i]][z[j]] for j in range(N)] for i in range(N)],
            [[W[x[i]][z[j]] for j in range(N)] for i in range(N)])
def build(G, shape):
    """shape: list of (K, count).  Returns r, rep[v] (Brent variable -> free variable id) and the orbit layout."""
    subs = subgroups(G)
    # free variables per representative: 48 symbolic entries, identified under K by union-find
    products = []   # list of (U, V, W) with entries = free-variable ids (ints)
    nfree = 0; parent = {}
    def find(a):
        while parent.get(a, a) != a: a = parent[a]
        return a
    def union(a, b):
        a, b = find(a), find(b)
        if a != b: parent[max(a, b)] = min(a, b)
    for kidx, cnt in shape:
        K = subs[kidx]
        for _ in range(cnt):
            base = nfree; nfree += 3 * N * N
            U = [[base + i * N + j for j in range(N)] for i in range(N)]
            V = [[base + N * N + i * N + j for j in range(N)] for i in range(N)]
            W = [[base + 2 * N * N + i * N + j for j in range(N)] for i in range(N)]
            for k in K:
                U2, V2, W2 = act(k, U, V, W)
                for i in range(N):
                    for j in range(N):
                        union(U[i][j], U2[i][j]); union(V[i][j], V2[i][j]); union(W[i][j], W2[i][j])
            # coset representatives of K in G: distinct images of the representative
            seen = set(); members = []
            for g in G:
                img = act(g, U, V, W)
                key = tuple(tuple(tuple(find(v) for v in row) for row in M) for M in img)
                if key not in seen: seen.add(key); members.append(img)
            assert len(members) == len(G) // len(K), (len(members), len(G), len(K))
            products += members
    r = len(products)
    nn = N * N
    rep = {}
    for m, (U, V, W) in enumerate(products):
        for i in range(N):
            for j in range(N):
                rep[m * nn + i * N + j] = find(U[i][j])
                rep[r * nn + m * nn + i * N + j] = find(V[i][j])
                rep[2 * r * nn + m * nn + i * N + j] = find(W[i][j])
    # renumber free variables densely
    ids = sorted(set(rep.values())); dense = {v: k for k, v in enumerate(ids)}
    rep = {k: dense[v] for k, v in rep.items()}
    return r, rep, len(ids)
def reduced_equations(G, shape):
    r, rep, nf = build(G, shape)
    seen, eqs = set(), []
    for mons, rhs in brent_equations(N, N, N, r):
        cnt = {}
        for mon in mons:
            q = tuple(sorted(set(rep[v] for v in mon)))
            cnt[q] = cnt.get(q, 0) ^ 1
        odd = frozenset(q for q, c in cnt.items() if c)
        if not odd:
            if rhs: return r, None, nf
            continue
        key = (odd, rhs)
        if key not in seen: seen.add(key); eqs.append((sorted(odd), rhs))
    return r, eqs, nf
def normalizer(G):
    """The normalizer of G in the permutation sandwich group S4^3 (elements mapping G-invariant schemes to
    G-invariant schemes)."""
    Gs = set(G)
    def pinv(p):
        q = [0] * N
        for i, x in enumerate(p): q[x] = i
        return tuple(q)
    S4 = list(itertools.permutations(range(N)))
    return [n for n in itertools.product(S4, S4, S4)
            if all(gcomp(gcomp(n, g), tuple(pinv(x) for x in n)) in Gs for g in G)]
def symmetry_generators(G, shape, max_cosets=24):
    """Free-variable permutations that are symmetries of the quotient (dict free var -> free var): swaps of
    consecutive orbits of the same type (the products are unordered), and the induced action of coset
    representatives of G in its normalizer (per orbit the coset member normalizing the orbit's stabilizer, so the
    representative block maps onto itself).  All are invisible to a clause-graph symmetry tool except one: the XOR
    ladders fix the monomial order, so only maps fixing every U variable are syntactic (2026-11-09 audit)."""
    subs = subgroups(G); r, rep, nf = build(G, shape); nn = N * N
    orbits = []; p0 = 0
    for kidx, cnt in shape:
        K = subs[kidx]
        for _ in range(cnt):
            U = [[rep[p0 * nn + i * N + j] for j in range(N)] for i in range(N)]
            V = [[rep[r * nn + p0 * nn + i * N + j] for j in range(N)] for i in range(N)]
            W = [[rep[2 * r * nn + p0 * nn + i * N + j] for j in range(N)] for i in range(N)]
            orbits.append((kidx, set(K), U, V, W)); p0 += len(G) // len(K)
    gens = []
    for a in range(len(orbits) - 1):
        if orbits[a][0] != orbits[a + 1][0]: continue
        pi = {v: v for v in range(nf)}
        for Ma, Mb in zip(orbits[a][2:], orbits[a + 1][2:]):
            for i in range(N):
                for j in range(N): pi[Ma[i][j]] = Mb[i][j]; pi[Mb[i][j]] = Ma[i][j]
        gens.append(pi)
    Gs = set(G)
    def pinv(p):
        q = [0] * N
        for i, x in enumerate(p): q[x] = i
        return tuple(q)
    def conj(n, g): return gcomp(gcomp(n, g), tuple(pinv(x) for x in n))
    seen = set()
    for n in normalizer(G):
        if n in Gs: continue
        coset = frozenset(gcomp(h, n) for h in G)
        if coset in seen: continue
        seen.add(coset)
        pi = {}; ok = True
        for kidx, K, U, V, W in orbits:
            n1 = next((c for c in coset if set(conj(c, k) for k in K) == K), None)
            if n1 is None: ok = False; break
            x, y, z = n1
            for i in range(N):
                for j in range(N):
                    for M, (a, b) in ((U, (x[i], y[j])), (V, (y[i], z[j])), (W, (x[i], z[j]))):
                        f, g = M[i][j], M[a][b]
                        if pi.get(f, g) != g: ok = False
                        pi[f] = g
        if ok and len(pi) == nf and len(set(pi.values())) == nf: gens.append(pi)
        if len(seen) >= max_cosets: break
    return gens
def lex_leader_clauses(pi, nf, nv, clauses):
    """x <=lex x o pi over the free variables in id order, fixed points skipped (Crawford et al.; implication
    encoding: sound for any set of group elements under one variable order).  Returns the new variable count."""
    pos = [v for v in range(nf) if pi[v] != v]
    e = None
    for idx, v in enumerate(pos):
        a, b = v + 1, pi[v] + 1
        pre = [] if e is None else [-e]
        clauses.append(pre + [-a, b])
        if idx + 1 < len(pos):
            nv += 1; clauses.append(pre + [-a, -b, nv]); clauses.append(pre + [a, b, nv]); e = nv
    return nv
def write_cnf(G, shape, out, lex=False):
    r, eqs, nf = reduced_equations(G, shape)
    if eqs is None:
        open(out, "w").write(f"c structurally UNSAT r={r}\np cnf 1 2\n1 0\n-1 0\n"); return r, None
    nv = nf; clauses = []; monvar = {}
    def lit_of(mon):
        nonlocal nv
        if len(mon) == 1: return mon[0] + 1
        if mon not in monvar:
            nv += 1; monvar[mon] = nv
            for x in mon: clauses.append([-nv, x + 1])
            clauses.append([nv] + [-(x + 1) for x in mon])
        return monvar[mon]
    for mons, rhs in eqs:
        lits = [lit_of(tuple(m)) for m in mons]; cur = lits[0]
        for l in lits[1:]:
            nv += 1; o = nv
            clauses += [[-o, cur, l], [-o, -cur, -l], [o, -cur, l], [o, cur, -l]]; cur = o
        clauses.append([cur] if rhs else [-cur])
    ngen = 0
    if lex:
        for pi in symmetry_generators(G, shape):
            nv = lex_leader_clauses(pi, nf, nv, clauses); ngen += 1
    with open(out, "w") as f:
        f.write(f"c sandwich-group quotient <4,4,4> r={r} shape {shape} {len(eqs)} equations {nf} free scheme vars"
                + (f"; lex-leader symmetry breaking for {ngen} generators" if lex else "") + "\n")
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for c in clauses: f.write(" ".join(map(str, c)) + " 0\n")
    return r, (len(eqs), nf, nv, len(clauses))
def decode(G, shape, solver_out, out_bits):
    r, rep, nf = build(G, shape)
    val = {}
    for ln in open(solver_out):
        if ln.startswith("v "):
            for tok in ln.split()[1:]:
                x = int(tok)
                if x: val[abs(x) - 1] = x > 0
    nn = N * N
    bits = [int(val.get(rep[v], False)) for v in range(3 * r * nn)]
    # full Brent check from scratch
    bad = 0
    for mons, rhs in brent_equations(N, N, N, r):
        s = 0
        for mon in mons:
            if all(bits[v] for v in mon): s ^= 1
        if s != rhs: bad += 1
    if bad: raise SystemExit(f"decoded scheme violates {bad} Brent equations")
    # distinct products?
    prods = {tuple(bits[m*nn:(m+1)*nn] + bits[r*nn+m*nn:r*nn+(m+1)*nn] + bits[2*r*nn+m*nn:2*r*nn+(m+1)*nn]) for m in range(r)}
    open(out_bits, "w").write("".join(map(str, bits)) + "\n")
    return r, len(prods)
def parse_shape(s): return [(int(a), int(b)) for a, b in (t.split(":") for t in s.split(","))]
if __name__ == "__main__":
    a = sys.argv[1:]
    G = GROUPS[a[a.index("--group") + 1]]
    if "--list" in a:
        for i, K in enumerate(subgroups(G)): print(i, "order", len(K), "orbit size", len(G) // len(K), K[:2] if len(K) <= 2 else K[:1])
        sys.exit()
    shape = parse_shape(a[a.index("--shape") + 1])
    if "decode" in a:
        i = a.index("decode"); r, nd = decode(G, shape, a[i + 1], a[i + 2]); print(f"decoded rank {r}, {nd} distinct products, Brent OK -> {a[i + 2]}")
    else:
        r, info = write_cnf(G, shape, a[-1], lex="--lex" in a); print(f"{a[-1]}: r={r} {'structurally UNSAT' if info is None else 'equations %d, free vars %d, cnf vars %d, clauses %d' % info}")
