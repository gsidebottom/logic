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
    # majority carries whose six clauses are spread over three 3-variable scopes:
    # for each pair of input literals (li, lj) the clauses (¬li ∨ ¬lj ∨ o) and (li ∨ lj ∨ ¬o)
    clause_set = {frozenset(c): i for i, c in enumerate(clauses)}
    pairs = collections.defaultdict(dict)   # output literal -> {frozenset(li, lj): (clause indices)}
    for scope, idxs in by_scope.items():
        if len(scope) != 3 or len(idxs) < 2: continue
        tern = [i for i in idxs if len(clauses[i]) == 3]
        for i in tern:
            c = clauses[i]
            for o in c:
                ins = [-l for l in c if l != o]          # (¬li ∨ ¬lj ∨ o) → li, lj
                j = clause_set.get(frozenset(ins + [-o]))   # (li ∨ lj ∨ ¬o)
                if j is not None: pairs[o][frozenset(ins)] = (i, j)
    for o, pr in pairs.items():
        if abs(o) in defined or len(pr) < 3: continue
        lits = set()
        for pq in pr: lits |= pq
        for trio in itertools.combinations(sorted(lits), 3):
            combos = [frozenset(x) for x in itertools.combinations(trio, 2)]
            if all(c in pr for c in combos) and abs(o) not in defined and len({abs(l) for l in trio}) == 3:
                cls = [i for c in combos for i in pr[c]]
                pos = o > 0
                gates.append(Gate("maj3", abs(o), list(trio), cls, (lambda vals, pos=pos: (sum(vals) >= 2) == pos)))
                defined.add(abs(o)); break
    return gates

def lit_value(lit, val_of_var):
    v = val_of_var[abs(lit)]
    return v if lit > 0 else (not v)

# ── cones ───────────────────────────────────────────────────────────────────
# A unit is one gate, or a full adder (an XOR3 and a MAJ3 over the same inputs:
# one unit, two outputs).  A cone is a set of units with inputs (variables fed
# from outside), outputs (unit outputs consumed outside, or observable) and
# hidden outputs (consumed only inside): merging a producer cone into its
# consumer's is always sound — an output stays visible while something outside
# reads it — and hides what it can.  Bounded by K inputs and MAXCOLS columns.
MAXCOLS = 14

class Unit:
    __slots__ = ("gates", "outs", "ins")
    def __init__(self, gates):
        self.gates = gates                       # evaluation order
        self.outs = [g.out for g in gates]
        self.ins = sorted({abs(l) for g in gates for l in g.inputs} - set(self.outs))

def make_units(gates):
    by_inputs = collections.defaultdict(list)
    for g in gates:
        if g.kind in ("xor3", "maj3"): by_inputs[frozenset(abs(l) for l in g.inputs)].append(g)
    used, units = set(), []
    for ins, gs in by_inputs.items():
        xs = [g for g in gs if g.kind == "xor3"]; ms = [g for g in gs if g.kind == "maj3"]
        for x, m in zip(xs, ms):
            units.append(Unit([x, m])); used.add(x.out); used.add(m.out)
    for g in gates:
        if g.out not in used: units.append(Unit([g]))
    return units

def build_cones(nv, clauses, gates, K):
    units = make_units(gates)
    unit_of = {}                       # output var -> unit
    for u in units:
        for o in u.outs: unit_of[o] = u
    in_def = collections.defaultdict(set); consumers = collections.defaultdict(set)
    for u in units:
        for g in u.gates:
            for i in g.clauses:
                in_def[g.out].add(i)
                for l in g.inputs: in_def[abs(l)].add(i)
            for l in g.inputs: consumers[abs(l)].add(id(u))
    occ = collections.defaultdict(set)
    for i, c in enumerate(clauses):
        for l in c: occ[abs(l)].add(i)
    observable = {v for v in unit_of if occ[v] - in_def[v]}
    # topological order of units; units on cycles are dropped
    uid = {id(u): u for u in units}
    indeg = {id(u): sum(1 for v in u.ins if v in unit_of) for u in units}
    order, queue = [], collections.deque(k for k, d in indeg.items() if d == 0)
    while queue:
        k = queue.popleft(); order.append(k)
        for o in uid[k].outs:
            for c in consumers.get(o, ()):
                if c in indeg:
                    indeg[c] -= 1
                    if indeg[c] == 0: queue.append(c)
    cyclic = [uid[k] for k in indeg if k not in set(order)]
    for u in cyclic:
        for o in u.outs: unit_of.pop(o, None)
    ordered = [uid[k] for k in order]
    # bottom-up merging
    cone = {}          # id(unit) -> dict(members=[units], inputs=set)
    absorbed = set()
    for u in ordered:
        members, inputs = [u], set(u.ins)
        changed = True
        while changed:
            changed = False
            for v in sorted(inputs):
                pu = unit_of.get(v)
                if pu is None or id(pu) in absorbed or id(pu) not in cone or pu is u: continue
                pc = cone[id(pu)]
                m_members = pc["members"] + members
                m_inputs = (inputs | pc["inputs"]) - {o for m in m_members for o in m.outs}
                inside = {id(m) for m in m_members}
                visible = [o for m in m_members for o in m.outs if o in observable or (consumers[o] - inside)]
                if len(m_inputs) > K or len(m_inputs) + len(visible) > MAXCOLS: continue
                members, inputs = m_members, m_inputs; absorbed.add(id(pu)); changed = True
        cone[id(u)] = {"members": members, "inputs": inputs}
    roots = [k for k in cone if k not in absorbed]
    result = []
    for k in roots:
        c = cone[k]; inside = {id(m) for m in c["members"]}
        outs = [o for m in c["members"] for o in m.outs]
        visible = [o for o in outs if o in observable or (consumers[o] - inside)]
        hidden = [o for o in outs if o not in visible]
        result.append({"members": c["members"], "inputs": sorted(c["inputs"]), "visible": visible, "hidden": hidden})
    return result, len(cyclic), len(units)

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

def cone_table(cone):
    """Columns: inputs then visible outputs.  Rows: a cube cover of the relation
    {(x, F(x))}, F the cone's function (hidden outputs evaluated inside)."""
    inputs, visible = cone["inputs"], cone["visible"]
    k, kv = len(inputs), len(visible)
    idx = {v: i for i, v in enumerate(inputs)}
    # members in dependency order (merging may have placed a producer after its consumer)
    pending, ordered, known = list(cone["members"]), [], set(inputs)
    while pending:
        ready = [m for m in pending if all(abs(l) in known for g in m.gates for l in g.inputs if abs(l) not in m.outs)]
        if not ready: raise RuntimeError("cone members do not form a DAG")
        for m in ready:
            ordered.append(m); known.update(m.outs); pending.remove(m)
    gates = [g for m in ordered for g in m.gates]
    val = {}; minterms = []; f = []
    for a in range(1 << k):
        for v, i in idx.items(): val[v] = bool(a >> i & 1)
        for g in gates: val[g.out] = g.fn([lit_value(l, val) for l in g.inputs])
        y = 0
        for j, o in enumerate(visible):
            if val[o]: y |= 1 << j
        minterms.append(a | (y << k)); f.append(y)
    cubes = qm_cover(k + kv, minterms)
    rows = [[None if m >> i & 1 else int(v >> i & 1) for i in range(k + kv)] for v, m in cubes]
    return rows, tuple(f)

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
    cones, ncyclic, nunits = build_cones(nv, clauses, gates, args.k)
    os.makedirs(os.path.join(args.out, "tables"), exist_ok=True)
    instances, absorbed_clauses, tables = [], set(), {}
    cone_records = []
    explain = set()   # absorbed clauses of the cones with no hidden variable: explanation-only clauses for the engine
    nhidden = 0; sizes = collections.Counter(); nfa = sum(1 for c in cones for m in c["members"] if len(m.gates) == 2)
    for cone in cones:
        ngates = sum(len(m.gates) for m in cone["members"])
        if ngates < args.min_gates or not cone["visible"] and not cone["hidden"]: continue
        rows, f = cone_table(cone)
        k, kv = len(cone["inputs"]), len(cone["visible"])
        if args.verify:
            for a in range(1 << k):
                bits = [a >> i & 1 for i in range(k)]
                fit = [r for r in rows if all(c is None or c == b for c, b in zip(r[:k], bits))]
                ys = {tuple(r[k:]) for r in fit}
                want = tuple(f[a] >> j & 1 for j in range(kv))
                assert all(all(c is None or c == w for c, w in zip(y, want)) for y in ys) and ys, f"cone {cone['visible']}: input {bits} → rows {ys}, function {want}"
        key = (k, kv, f)
        if key not in tables:
            name = f"t{len(tables)}.json"
            json.dump({"name": name[:-5], "vars": [f"i{j}" for j in range(k)] + [f"o{j}" for j in range(kv)], "rows": rows},
                      open(os.path.join(args.out, "tables", name), "w"))
            tables[key] = name
        instances.append({"table": "tables/" + tables[key], "args": cone["inputs"] + cone["visible"]})
        # the cone's own clauses, for a per-cone selection (tools/select_cones.py)
        cone_records.append({"instance": len(instances) - 1, "inputs": cone["inputs"], "visible": cone["visible"],
                             "hidden": cone["hidden"], "clauses": sorted({ci for m in cone["members"] for g in m.gates for ci in g.clauses})})
        for m in cone["members"]:
            for g in m.gates: absorbed_clauses.update(g.clauses)
        if not cone["hidden"]:
            for m in cone["members"]:
                for g in m.gates: explain.update(g.clauses)
        nhidden += len(cone["hidden"]); sizes[ngates] += 1
    with open(os.path.join(args.out, "residual.cnf"), "w") as out:
        rest = [c for i, c in enumerate(clauses) if i not in absorbed_clauses]
        out.write(f"p cnf {nv} {len(rest)}\n")
        for c in rest: out.write(" ".join(map(str, c)) + " 0\n")
    json.dump(instances, open(os.path.join(args.out, "boxes.json"), "w"))
    for r in cone_records: r["clauses"] = [clauses[i] for i in r["clauses"]]
    json.dump(cone_records, open(os.path.join(args.out, "cones.json"), "w"))
    # the clauses the boxes stand for: `sat -b boxes --proof` derives every
    # box propagation from these, so residual + absorbed = the original CNF
    # is the formula the DRAT proof certifies
    with open(os.path.join(args.out, "absorbed.cnf"), "w") as out:
        ab = [clauses[i] for i in sorted(absorbed_clauses)]
        out.write(f"p cnf {nv} {len(ab)}\n")
        for c in ab: out.write(" ".join(map(str, c)) + " 0\n")
    with open(os.path.join(args.out, "explain.cnf"), "w") as out:
        xs = [clauses[i] for i in sorted(explain)]
        out.write(f"p cnf {nv} {len(xs)}\n")
        for c in xs: out.write(" ".join(map(str, c)) + " 0\n")
    print(f"{os.path.basename(args.cnf)}: {nv} vars, {len(clauses)} clauses; gates {dict(kinds)} ({nunits} units, {nfa} full adders, {ncyclic} dropped on cycles); "
          f"cones {len(instances)} (gates per cone {dict(sorted(sizes.items()))}), {len(tables)} distinct tables, {nhidden} hidden vars, "
          f"{len(absorbed_clauses)} clauses absorbed, {len(rest)} residual, {len(xs)} explanation-only (cones with visible outputs)")

if __name__ == "__main__":
    main()
