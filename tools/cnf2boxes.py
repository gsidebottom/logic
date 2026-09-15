#!/usr/bin/env python3
"""CNF → box constraints: read the Tseitin gates off a CNF, merge single-fanout
gates into cones of at most K inputs, compile each cone to a table over its
inputs and output (the cone's internal gate outputs are hidden — they are
functions of the inputs and occur nowhere else), and write what `sat -b
boxes --boxes` takes: the residual CNF (the clauses no cone absorbed) and
the box instances.

    tools/cnf2boxes.py in.cnf[.xz] --out DIR [--k 8] [--min-gates 2]
    xz -dc in.cnf.xz | sat -b boxes --boxes DIR/boxes.json   # no: use the residual
    sat -b boxes --boxes DIR/boxes.json < DIR/residual.cnf

Gates recognised: AND/OR of any width (o ∨ ¬a1 ∨ … ∨ ¬ak with ¬o ∨ ai),
XOR2 (4 ternary clauses over 3 variables forbidding one parity class; the
largest variable is taken as the output — a cycle check removes wrong
guesses), XOR3 (8 clauses over 4 variables), MAJ3 (6 ternary clauses).
"""
import argparse, collections, itertools, json, lzma, os, sys

# ── CNF ─────────────────────────────────────────────────────────────────────
def read_cnf(path):
    opener = lzma.open if path.endswith(".xz") else open
    clauses, nv = [], 0
    with opener(path, "rt", errors="replace") as f:
        for line in f:
            if not line or line[0] in "cp%":
                if line.startswith("p cnf"): nv = int(line.split()[2])
                continue
            lits = [int(x) for x in line.split()]
            if lits and lits[-1] == 0: lits = lits[:-1]
            if lits: clauses.append(tuple(lits))
    return nv, clauses

# ── gates ───────────────────────────────────────────────────────────────────
class Gate:
    __slots__ = ("kind", "out", "inputs", "clauses", "fn")
    def __init__(self, kind, out, inputs, clauses, fn):
        self.kind, self.out, self.inputs, self.clauses, self.fn = kind, out, inputs, clauses, fn
        # out: variable; inputs: list of literals (signed ints); clauses: indices;
        # fn(values of input literals as bools) -> value of the output *variable*

def extract_gates(clauses):
    binset = {}
    for i, c in enumerate(clauses):
        if len(c) == 2: binset.setdefault(frozenset(c), i)
    by_scope = collections.defaultdict(list)
    for i, c in enumerate(clauses): by_scope[frozenset(abs(l) for l in c)].append(i)
    gates, defined = [], set()
    # AND / OR
    for i, c in enumerate(clauses):
        if len(c) < 3: continue
        for o in c:
            if abs(o) in defined: continue
            bins = []
            for l in c:
                if l == o: continue
                j = binset.get(frozenset((-o, -l)))
                if j is None: break
                bins.append(j)
            else:
                # o ⇔ ∧ (¬l): with o = var: var = AND(¬l); with o = ¬var: var = ¬AND(¬l) = OR(l)
                ins = [-l for l in c if l != o]
                pos = o > 0
                gates.append(Gate("and", abs(o), ins, [i] + bins, (lambda vals, pos=pos: all(vals) == pos)))
                defined.add(abs(o)); break
    # parity and majority from same-scope groups
    for scope, idxs in by_scope.items():
        k = len(scope)
        if k not in (3, 4): continue
        group = [clauses[i] for i in idxs]
        if k == 3 and len(group) == 4 and all(len(c) == 3 for c in group):
            par = {sum(1 for l in c if l > 0) % 2 for c in group}
            if len(par) == 1:
                # the forbidden assignments have (#true lits ... ) — the clauses forbid the
                # assignments with parity of true variables == p:  x⊕y⊕z = 1-p
                p = par.pop()
                out = max(scope)
                if out in defined: continue
                ins = [v for v in sorted(scope) if v != out]
                target = 1 - p  # x ⊕ y ⊕ z must equal target … derive: a clause forbids the assignment where all its literals are false
                # each clause (l1∨l2∨l3) forbids l1=l2=l3=false: variables true iff literal negative;
                # #true vars = #negative lits = 3 - (#positive) ≡ 1 - p (mod 2): forbidden parity of true vars is (1-p)%2, so required parity is p
                req = p
                gates.append(Gate("xor2", out, ins, list(idxs), (lambda vals, req=req: (sum(vals) % 2) != req)))
                defined.add(out)
        if k == 4:
            quads = [i for i in idxs if len(clauses[i]) == 4]
            terns = [i for i in idxs if len(clauses[i]) == 3]
            if len(quads) == 8:
                par = {sum(1 for l in clauses[i] if l > 0) % 2 for i in quads}
                if len(par) == 1:
                    p = par.pop(); out = max(scope)
                    if out not in defined:
                        ins = [v for v in sorted(scope) if v != out]
                        # forbidden: #true vars = 4 - #pos ≡ p (mod 2) → required parity of true vars = 1-p; out = parity(ins) xor ...
                        # true-var parity of (ins + out) must be (1-p): out = (sum(ins) + 1 - p) % 2
                        gates.append(Gate("xor3", out, ins, quads, (lambda vals, p=p: (sum(vals) + 1 - p) % 2 == 1)))
                        defined.add(out)
            if len(terns) == 6:
                tset = {frozenset(clauses[i]) for i in terns}
                for o in scope:
                    ins = [v for v in scope if v != o]
                    need = set()
                    for a, b in itertools.combinations(ins, 2):
                        need.add(frozenset((-a, -b, o))); need.add(frozenset((a, b, -o)))
                    if need == tset and o not in defined:
                        gates.append(Gate("maj3", o, sorted(ins), terns, (lambda vals: sum(vals) >= 2)))
                        defined.add(o); break
    return gates

def lit_value(lit, val_of_var):
    v = val_of_var[abs(lit)]
    return v if lit > 0 else (not v)

# ── cones ───────────────────────────────────────────────────────────────────
def build_cones(nv, clauses, gates, K):
    gate_of = {g.out: g for g in gates}
    # occurrences outside gate definitions decide what may be hidden
    in_def = collections.defaultdict(set)   # var -> clause indices that define or consume it inside gates
    consumers = collections.defaultdict(set)  # var -> gates (outputs) that take it as input
    for g in gates:
        for i in g.clauses: in_def[g.out].add(i)
        for l in g.inputs:
            consumers[abs(l)].add(g.out)
            for i in g.clauses: in_def[abs(l)].add(i)
    occ = collections.defaultdict(set)
    for i, c in enumerate(clauses):
        for l in c: occ[abs(l)].add(i)
    observable = {v for v in gate_of if occ[v] - in_def[v]}   # used by a non-gate clause: stays visible
    # topological order of gates (inputs first); drop gates on cycles
    indeg = {g.out: sum(1 for l in g.inputs if abs(l) in gate_of) for g in gates}
    order, queue = [], collections.deque(v for v, d in indeg.items() if d == 0)
    while queue:
        v = queue.popleft(); order.append(v)
        for w in consumers.get(v, ()):
            if w in indeg:
                indeg[w] -= 1
                if indeg[w] == 0: queue.append(w)
    cyclic = set(gate_of) - set(order)
    for v in cyclic: del gate_of[v]
    gates = [gate_of[v] for v in order if v in gate_of]
    # bottom-up merging: a cone is (root, members, inputs); a single-fanout, unobservable
    # gate output whose only consumer is the root is hidden if the merged inputs fit in K
    cone_of = {}     # root -> dict(members=[outs], inputs=set(vars))
    absorbed = set()
    for g in gates:
        members, inputs = [g.out], {abs(l) for l in g.inputs}
        changed = True
        while changed:
            changed = False
            for v in sorted(inputs):
                h = gate_of.get(v)
                if h is None or v in observable or consumers[v] != {g.out} or v not in cone_of or v in absorbed: continue
                merged = (inputs - {v}) | cone_of[v]["inputs"]
                if len(merged) > K: continue
                inputs = merged; members = cone_of[v]["members"] + members; absorbed.add(v); changed = True
        cone_of[g.out] = {"members": members, "inputs": inputs}
    roots = [v for v in cone_of if v not in absorbed]
    return gate_of, cone_of, roots, cyclic

# ── tables ──────────────────────────────────────────────────────────────────
def qm_cover(k, minterms):
    """A small irredundant cover of the minterms (bit i of an index = column i):
    Quine–McCluskey primes, then essential + greedy cover.  Returns cubes as
    (value, mask) with mask bits = don't-cares."""
    if not minterms: return []
    level = {(m, 0) for m in minterms}
    primes = []
    while level:
        merged, nxt = set(), set()
        for v, m in level:
            for b in range(k):
                bit = 1 << b
                if m & bit or v & bit: continue
                if (v | bit, m) in level:
                    nxt.add((v, m | bit)); merged.add((v, m)); merged.add((v | bit, m))
        primes += [c for c in level if c not in merged]
        level = nxt
    # cover
    def covers(c, x): v, m = c; return (x & ~m) == (v & ~m)
    uncovered = set(minterms); chosen = []
    by_min = {x: [c for c in primes if covers(c, x)] for x in minterms}
    for x, cs in by_min.items():
        if len(cs) == 1 and cs[0] not in chosen:
            chosen.append(cs[0]); uncovered -= {y for y in uncovered if covers(cs[0], y)}
    while uncovered:
        best = max(primes, key=lambda c: sum(1 for y in uncovered if covers(c, y)))
        chosen.append(best); uncovered -= {y for y in uncovered if covers(best, y)}
    return chosen

def cone_table(cone, gate_of, K):
    inputs = sorted(cone["inputs"]); members = cone["members"]; root = members[-1]
    k = len(inputs)
    idx = {v: i for i, v in enumerate(inputs)}
    f = []
    val = {}
    for a in range(1 << k):
        for v, i in idx.items(): val[v] = bool(a >> i & 1)
        for m in members:      # topological within the cone (absorbed cones precede their consumer)
            g = gate_of[m]
            val[m] = g.fn([lit_value(l, val) for l in g.inputs])
        f.append(val[root])
    ones = [a for a in range(1 << k) if f[a]]; zeros = [a for a in range(1 << k) if not f[a]]
    rows = []
    for cubes, o in ((qm_cover(k, ones), 1), (qm_cover(k, zeros), 0)):
        for v, m in cubes:
            rows.append([None if m >> i & 1 else int(v >> i & 1) for i in range(k)] + [o])
    return inputs, root, rows, tuple(f)

# ── main ────────────────────────────────────────────────────────────────────
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cnf"); ap.add_argument("--out", required=True)
    ap.add_argument("--k", type=int, default=8, help="max cone inputs (table columns − 1)")
    ap.add_argument("--min-gates", type=int, default=2, help="emit a cone only with this many gates")
    ap.add_argument("--verify", action="store_true", help="check every table against its cone function (slow for large k)")
    args = ap.parse_args()
    nv, clauses = read_cnf(args.cnf)
    gates = extract_gates(clauses)
    kinds = collections.Counter(g.kind for g in gates)
    gate_of, cone_of, roots, cyclic = build_cones(nv, clauses, gates, args.k)
    os.makedirs(os.path.join(args.out, "tables"), exist_ok=True)
    instances, absorbed_clauses, tables = [], set(), {}
    nhidden = 0; sizes = collections.Counter()
    for r in roots:
        cone = cone_of[r]
        if len(cone["members"]) < args.min_gates: continue
        inputs, root, rows, f = cone_table(cone, gate_of, args.k)
        if args.verify:
            k = len(inputs)
            for a in range(1 << k):
                bits = [a >> i & 1 for i in range(k)]
                fit = [r for r in rows if all(c is None or c == b for c, b in zip(r[:-1], bits))]
                outs = {r[-1] for r in fit}
                assert outs == {int(f[a])}, f"cone {root}: input {bits} → rows give {outs}, function {int(f[a])}"
        key = (len(inputs), f)
        if key not in tables:
            name = f"t{len(tables)}.json"
            json.dump({"name": name[:-5], "vars": [f"i{j}" for j in range(len(inputs))] + ["o"], "rows": rows},
                      open(os.path.join(args.out, "tables", name), "w"))
            tables[key] = name
        instances.append({"table": "tables/" + tables[key], "args": inputs + [root]})
        for m in cone["members"]: absorbed_clauses.update(gate_of[m].clauses)
        nhidden += len(cone["members"]) - 1; sizes[len(cone["members"])] += 1
    with open(os.path.join(args.out, "residual.cnf"), "w") as out:
        rest = [c for i, c in enumerate(clauses) if i not in absorbed_clauses]
        out.write(f"p cnf {nv} {len(rest)}\n")
        for c in rest: out.write(" ".join(map(str, c)) + " 0\n")
    json.dump(instances, open(os.path.join(args.out, "boxes.json"), "w"))
    print(f"{os.path.basename(args.cnf)}: {nv} vars, {len(clauses)} clauses; gates {dict(kinds)} ({len(cyclic)} dropped on cycles); "
          f"cones {len(instances)} (sizes {dict(sorted(sizes.items()))}), {len(tables)} distinct tables, {nhidden} hidden vars, "
          f"{len(absorbed_clauses)} clauses absorbed, {len(rest)} residual")

if __name__ == "__main__":
    main()
