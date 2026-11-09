#!/usr/bin/env python3
"""Colour refinement (1-WL) on the literal/clause graph of a DIMACS CNF.
If the stable partition is discrete, the CNF has no syntactic symmetry
(no non-trivial clause-graph automorphism), so dejavu/satsuma can find nothing.
Prints the number of colour classes after each round and the final verdict."""
import sys, hashlib
path = sys.argv[1]
clauses = []
nv = 0
with open(path) as f:
    for ln in f:
        if ln[0] in 'cp':
            if ln[0] == 'p': nv = int(ln.split()[2])
            continue
        lits = [int(t) for t in ln.split()]
        if lits and lits[-1] == 0: lits.pop()
        if lits: clauses.append(lits)
# vertices: literal l -> index (l>0: l-1, l<0: nv-l-1), clause c -> 2nv+c
V = 2 * nv + len(clauses)
adj = [[] for _ in range(V)]
def lix(l): return l - 1 if l > 0 else nv - l - 1
for v in range(nv):          # negation edge between the two literals of a variable
    adj[v].append(nv + v); adj[nv + v].append(v)
for c, lits in enumerate(clauses):
    cv = 2 * nv + c
    for l in lits:
        adj[lix(l)].append(cv); adj[cv].append(lix(l))
# initial colours: literal (0) vs clause (1) + clause length
col = [0] * V
for v in range(2 * nv): col[v] = 0
for c, lits in enumerate(clauses): col[2 * nv + c] = 1 + len(lits)
ncl = len(set(col)); rnd = 0
print(f"{path.split('/')[-1]}: {nv} vars, {len(clauses)} clauses, {V} vertices; initial classes {ncl}")
while True:
    rnd += 1
    sig = {}
    new = [0] * V
    for v in range(V):
        key = (col[v], tuple(sorted(col[u] for u in adj[v])))
        h = sig.get(key)
        if h is None: h = len(sig); sig[key] = h
        new[v] = h
    n2 = len(sig)
    print(f"round {rnd}: {n2} classes")
    col = new
    if n2 == ncl: break
    ncl = n2
    if ncl == V: break
if ncl == V:
    print("DISCRETE: no syntactic symmetry at all (automorphism group trivial)")
else:
    # sizes of non-singleton classes, restricted to variables (pair literal classes)
    from collections import Counter
    cnt = Counter(col)
    multi = [(c, n) for c, n in cnt.items() if n > 1]
    litmulti = [(c, n) for c, n in multi if any(col[v] == c for v in range(2 * nv))]
    print(f"non-discrete: {len(multi)} classes of size>1 (total {sum(n for _, n in multi)} vertices); among literals: {len(litmulti)} classes, {sum(n for _, n in litmulti)} literal vertices")
    print("largest literal classes:", sorted((n for _, n in litmulti), reverse=True)[:12])
