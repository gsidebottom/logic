#!/usr/bin/env python3
"""CNF -> AIG -> (ABC rewriting) -> CNF: circuit-aware preprocessing.

The gate definitions (AND/OR of any width, XOR2, XOR3, MAJ3, read off the
CNF by cnf2boxes.extract_gates) become an And-Inverter Graph whose primary
inputs are the undefined variables and whose primary outputs are the gate
outputs that other clauses mention; the clauses that are not gate
definitions are the residual.  ABC rewrites the AIG (its primary-output
functions are preserved), and the result is Tseitin-encoded back to CNF
with the residual appended, the primary inputs and outputs keeping their
original variable numbers.  Gate outputs nobody else mentions vanish with
their definitions; gates on definition cycles stay in the residual.

  cnf2aig.py in.cnf --aag out.aag --map out.map          # CNF -> AIGER (ascii)
  cnf2aig.py in.cnf --abc ABC --script resyn2 --out out.cnf   # the whole pipeline
  cnf2aig.py in.cnf --out out.cnf                          # round trip, no rewriting

The output is equisatisfiable with the input; every model of the output
restricted to the original variables is a model of the input.
"""
import argparse, collections, itertools, os, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cnf2boxes import read_cnf, extract_gates

SCRIPTS = {
    "none": "",
    "resyn2": "balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance",
    "resyn2f": "balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance; fraig",
    "dc2": "dc2",
    "dc2f": "dc2; fraig; dc2",
    "compress2": "balance -l; rewrite -l; refactor -l; balance -l; rewrite -l; rewrite -zl; balance -l; refactor -zl; rewrite -zl; balance -l",
}

def simplify_root(nv, clauses):
    """Unit propagation to its fixpoint and tautology removal, before gate
    extraction: some encodings pad binary clauses to three literals with a
    constant-true variable (the multiplier-verification family), which
    hides every gate from the pattern matcher.  Returns (clauses, units,
    unsat): the simplified clauses without the units, the unit literals
    (kept in the output), and whether the units contradict."""
    val = {}
    queue = [c[0] for c in clauses if len(c) == 1]
    units = []
    while queue:
        l = queue.pop()
        v = abs(l)
        if v in val:
            if val[v] != (l > 0): return clauses, units, True
            continue
        val[v] = l > 0; units.append(l)
        # (a full occurrence list would be faster; the fixpoint below reruns instead)
    changed = True; cur = clauses
    while changed:
        changed = False; out = []
        for c in cur:
            if len(c) == 1: continue
            seen = set(c)
            if any(-l in seen for l in c): continue        # tautology
            keep = []; sat = False
            for l in c:
                v = abs(l)
                if v in val:
                    if val[v] == (l > 0): sat = True; break
                    continue
                keep.append(l)
            if sat: continue
            if not keep: return clauses, units, True         # empty clause
            if len(keep) == 1:
                l = keep[0]; v = abs(l)
                if v in val and val[v] != (l > 0): return clauses, units, True
                if v not in val: val[v] = l > 0; units.append(l); changed = True
                continue
            if len(keep) != len(c): changed = True
            out.append(keep)
        cur = out
    return cur, units, False

def extract_gates_generic(clauses, gates, max_inputs=3):
    """Gates of any encoding: a variable o with candidate inputs In (the
    up to 'max_inputs' variables that co-occur with it most) is a gate when
    the clauses over {o} + In, and only those, say exactly "o = f(In)":
    every clause is satisfied by every row of f (so none constrains the
    inputs) and for every input assignment the clauses forbid the other
    value of o.  Then those clauses are equivalent to the definition and
    can be replaced by it.  Catches multiplexers, NAND/NOR, buffers and
    the padded encodings that the fixed patterns miss.  Clauses already
    claimed by a gate are not reused."""
    from cnf2boxes import Gate
    defined = {g.out for g in gates}
    used = set()
    for g in gates: used.update(g.clauses)
    occ = collections.defaultdict(list)
    for i, c in enumerate(clauses):
        if i in used or len(c) > 4: continue
        for l in c: occ[abs(l)].append(i)
    found = []
    # fewest occurrences first: a gate's output occurs in its definition
    # and a few uses, a circuit input in thousands of clauses (the 16x16
    # multiplier extracts to exactly its 32 inputs this way)
    for o in sorted(occ, key=lambda v: len(occ[v])):
        if o in defined: continue
        idxs = [i for i in occ[o] if i not in used]
        if not idxs: continue
        cnt = collections.Counter(abs(l) for i in idxs for l in clauses[i] if abs(l) != o)
        ranked = [v for v, _ in cnt.most_common(max_inputs + 2)]
        # the inputs of o's own definition tie in count with the outputs of
        # gates that use o: try every small subset of the best candidates,
        # largest first, and keep the first that defines o
        tried = set(); hit = None
        for k in range(min(max_inputs, len(ranked)), 0, -1):
          for In in itertools.combinations(ranked, k):
            inset = set(In)
            cidx = [i for i in idxs if all(abs(l) == o or abs(l) in inset for l in clauses[i])]
            key = frozenset(cidx)
            if not cidx or key in tried: continue
            tried.add(key)
            cls = [clauses[i] for i in cidx]
            pos = {v: j for j, v in enumerate(In)}
            table = []; ok = True
            for bits in itertools.product([False, True], repeat=k):
                vals = {In[j]: bits[j] for j in range(k)}
                allowed = []
                for ov in (False, True):
                    vals[o] = ov
                    if all(any((l > 0) == vals[abs(l)] for l in c) for c in cls): allowed.append(ov)
                if len(allowed) != 1: ok = False; break
                table.append(allowed[0])
            if not ok: continue
            # the rows satisfying these clauses are exactly the definition's
            # rows, so the clauses and "o = f(In)" are the same constraint
            hit = (list(In), cidx, table); break
          if hit: break
        if hit:
            In, cidx, tbl = hit
            # the table is in itertools.product order: the first input is the
            # most significant bit of the row index
            found.append(Gate("gen", o, In, cidx, (lambda vals, tbl=tbl, k=len(In): tbl[sum(int(v) << (k - 1 - j) for j, v in enumerate(vals))])))
            defined.add(o); used.update(cidx)
    return found

def build_aig(nv, clauses, gates):
    """Keep the acyclic gates; return (residual clause indices, pis, pos, ands, lit_of)."""
    out_gate = {}
    for g in gates:
        out_gate.setdefault(g.out, g)
    # drop gates on definition cycles (Kahn over the gate graph)
    indeg = {g.out: sum(1 for l in g.inputs if abs(l) in out_gate) for g in out_gate.values()}
    consumers = collections.defaultdict(list)
    for g in out_gate.values():
        for l in g.inputs:
            if abs(l) in out_gate: consumers[abs(l)].append(g.out)
    order, queue = [], collections.deque(o for o, d in indeg.items() if d == 0)
    while queue:
        o = queue.popleft(); order.append(o)
        for c in consumers[o]:
            indeg[c] -= 1
            if indeg[c] == 0: queue.append(c)
    kept = {o: out_gate[o] for o in order}
    ncyclic = len(out_gate) - len(kept)
    defclauses = set()
    for g in kept.values(): defclauses.update(g.clauses)
    residual = [i for i in range(len(clauses)) if i not in defclauses]
    mentioned = set()
    for i in residual:
        for l in clauses[i]: mentioned.add(abs(l))
    pis = sorted({abs(l) for g in kept.values() for l in g.inputs if abs(l) not in kept})
    pos = sorted(o for o in kept if o in mentioned)
    # AIG literals: 0 = false, 1 = true, var i -> 2i
    lit_of = {}
    nxt = [0]  # last AIG variable index used (inputs take 1..I)
    for v in pis:
        nxt[0] += 1; lit_of[v] = 2 * nxt[0]
    ands = []
    def new_and(a, b):
        if a == 0 or b == 0: return 0
        if a == 1: return b
        if b == 1: return a
        if a == b: return a
        if a == b ^ 1: return 0
        nxt[0] += 1; lhs = 2 * nxt[0]
        if a < b: a, b = b, a
        ands.append((lhs, a, b)); return lhs
    def and_list(ls):
        acc = 1
        for l in ls: acc = new_and(acc, l)
        return acc
    def or_list(ls):
        return and_list([l ^ 1 for l in ls]) ^ 1
    for o in order:
        g = kept[o]
        ins = [lit_of[abs(l)] ^ (1 if l < 0 else 0) for l in g.inputs]
        if g.kind == "and":
            # fn(vals) = all(vals) == pos, vals being the input LITERALS' values
            pos_ = g.fn([True] * len(ins))
            lit = and_list(ins) ^ (0 if pos_ else 1)
        else:
            # small gate: sum of the minterms of its truth table over the input variables
            k = len(ins); terms = []
            for bits in itertools.product([False, True], repeat=k):
                if g.fn(list(bits)):
                    terms.append(and_list([ins[j] ^ (0 if bits[j] else 1) for j in range(k)]))
            lit = or_list(terms) if terms else 0
        lit_of[o] = lit
    return residual, pis, pos, ands, lit_of, ncyclic

def write_aag(path, pis, pos, ands, lit_of):
    """ASCII AIGER (for reading by eye; ABC reads only the binary form)."""
    m = max([l // 2 for l in lit_of.values()] + [1])
    with open(path, "w") as f:
        f.write(f"aag {m} {len(pis)} 0 {len(pos)} {len(ands)}\n")
        for v in pis: f.write(f"{lit_of[v]}\n")
        for o in pos: f.write(f"{lit_of[o]}\n")
        for lhs, a, b in ands: f.write(f"{lhs} {a} {b}\n")

def write_aig(path, pis, pos, ands, lit_of):
    """Binary AIGER: inputs are the variables 1..I, the ANDs follow in
    order with consecutive variables, each as two delta-encoded numbers."""
    I, A = len(pis), len(ands)
    assert [lit_of[v] for v in pis] == [2 * (i + 1) for i in range(I)]
    def enc(x):
        out = bytearray()
        while True:
            b = x & 0x7f; x >>= 7
            if x: out.append(b | 0x80)
            else: out.append(b); return bytes(out)
    with open(path, "wb") as f:
        f.write(f"aig {I + A} {I} 0 {len(pos)} {A}\n".encode())
        for o in pos: f.write(f"{lit_of[o]}\n".encode())
        for i, (lhs, a, b) in enumerate(ands):
            assert lhs == 2 * (I + i + 1) and a >= b and lhs > a, (lhs, a, b)
            f.write(enc(lhs - a)); f.write(enc(a - b))

def read_aiger(path):
    """Binary or ascii AIGER; returns (M, I, L, O, A, inputs, outputs, ands)."""
    data = open(path, "rb").read()
    nl = data.index(b"\n"); head = data[:nl].decode().split(); pos = nl + 1
    kind = head[0]; M, I, L, O, A = map(int, head[1:6])
    assert L == 0, "latches are not expected"
    if kind == "aag":
        lines = data[pos:].decode().split("\n")
        inputs = [int(lines[i]) for i in range(I)]
        outputs = [int(lines[I + i]) for i in range(O)]
        ands = []
        for i in range(A):
            lhs, a, b = map(int, lines[I + O + i].split()); ands.append((lhs, a, b))
        return M, I, L, O, A, inputs, outputs, ands
    assert kind == "aig"
    inputs = [2 * (i + 1) for i in range(I)]
    outputs = []
    for _ in range(O):
        nl = data.index(b"\n", pos); outputs.append(int(data[pos:nl])); pos = nl + 1
    def decode():
        nonlocal pos
        x, shift = 0, 0
        while True:
            ch = data[pos]; pos += 1
            x |= (ch & 0x7f) << shift; shift += 7
            if not ch & 0x80: return x
    ands = []
    for i in range(A):
        lhs = 2 * (I + L + i + 1)
        d0 = decode(); d1 = decode()
        a = lhs - d0; b = a - d1
        ands.append((lhs, a, b))
    return M, I, L, O, A, inputs, outputs, ands

def aig_to_cnf(nv, clauses, residual, pis, pos, aig):
    """Tseitin the AIG; PIs and POs keep their original variables."""
    M, I, L, O, A, inputs, outputs, ands = aig
    assert I == len(pis) and O == len(pos)
    var_of = {}                        # AIG variable index -> CNF variable
    for v, lit in zip(pis, inputs): var_of[lit // 2] = v
    nxt = [nv]
    out_lits = list(outputs)
    # a PO driven by a plain AND node takes the original variable's number
    used = set(pis)
    for o, lit in zip(pos, out_lits):
        idx = lit // 2
        if lit & 1 == 0 and idx not in var_of and idx != 0:
            var_of[idx] = o; used.add(o)
    def cnf_var(idx):
        if idx not in var_of:
            nxt[0] += 1; var_of[idx] = nxt[0]
        return var_of[idx]
    def cnf_lit(lit):
        if lit == 0: return None   # false
        if lit == 1: return "T"    # true
        v = cnf_var(lit // 2); return -v if lit & 1 else v
    out = []
    for lhs, a, b in ands:
        x = cnf_lit(lhs); la, lb = cnf_lit(a), cnf_lit(b)
        # x <-> a & b, with constants folded
        for l in (la, lb):
            if l is None: out.append([-x]); break
        else:
            ta = None if la == "T" else la; tb = None if lb == "T" else lb
            if ta is None and tb is None: out.append([x]); continue
            for l in (ta, tb):
                if l is not None: out.append([-x, l])
            out.append([x] + [-l for l in (ta, tb) if l is not None])
    for o, lit in zip(pos, out_lits):
        l = cnf_lit(lit)
        if l is None: out.append([-o]); continue
        if l == "T": out.append([o]); continue
        if l == o: continue
        out.append([-o, l]); out.append([o, -l])
    for i in residual: out.append(list(clauses[i]))
    return nxt[0], out

def abc_cnf_to_cnf(nv, clauses, residual, pis, pos, path, I, A):
    """ABC's `&write_cnf -i -o`: CNF variable = GIA object id + 1, the GIA
    being the one `&w` wrote (constant 0, inputs 1..I, ands I+1..I+A,
    outputs I+A+1..I+A+O); no clause asserts the outputs, ids the cut
    mapping left unused are forced false.  Inputs and outputs take the
    original variables, every other id a fresh one; the residual follows."""
    rename = {}
    for k, v in enumerate(pis): rename[k + 2] = v
    for j, o in enumerate(pos): rename[I + A + 2 + j] = o
    pi_ids = set(range(2, I + 2))   # a unit on one of these is the writer's
    nxt = [nv]; out = []            # don't-care for an unused input: dropped
    def rn(l):
        x = abs(l)
        if x not in rename:
            nxt[0] += 1; rename[x] = nxt[0]
        return -rename[x] if l < 0 else rename[x]
    with open(path) as f:
        for line in f:
            if line.startswith("c") or line.startswith("p"): continue
            lits = [int(t) for t in line.split()]
            if lits and lits[-1] == 0: lits.pop()
            if len(lits) == 1 and abs(lits[0]) in pi_ids: continue
            if lits: out.append([rn(l) for l in lits])
    for i in residual: out.append(list(clauses[i]))
    return nxt[0], out

def write_cnf(path, nv, cls):
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls: f.write(" ".join(map(str, c)) + " 0\n")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cnf"); ap.add_argument("--out"); ap.add_argument("--aag", help="write the AIG here (.aig binary, .aag ascii)"); ap.add_argument("--map")
    ap.add_argument("--abc", help="path to the abc binary (rewrite when given)")
    ap.add_argument("--script", default="resyn2", help="|".join(SCRIPTS) + " or a literal abc command string")
    ap.add_argument("--keep", help="directory to keep the intermediate AIGER files")
    ap.add_argument("--backend", default="tseitin", choices=["tseitin", "abc"],
                    help="CNF of the rewritten AIG: one AND at a time (tseitin) or ABC's cut-based generator (abc)")
    a = ap.parse_args()
    nv, clauses0 = read_cnf(a.cnf)
    clauses, units, unsat = simplify_root(nv, clauses0)
    if unsat:
        print(f"{os.path.basename(a.cnf)}: the unit clauses contradict -- writing the empty clause", flush=True)
        if a.out: write_cnf(a.out, nv, [[]])
        return
    print(f"{os.path.basename(a.cnf)}: root simplification: {len(units)} units, {len(clauses0)} -> {len(clauses)} clauses", flush=True)
    # A symmetric XOR group can be oriented towards any of its variables.
    # The pattern matcher takes the highest-numbered one (the Tseitin
    # convention: sum-of-3-cubes, 1K of 113K gates on cycles that way, 82K
    # of 82K the other), the generic detector the least-used one (right for
    # other encoders); the wrong choice puts most gates on cycles, so both
    # are tried and the orientation with fewer cyclic gates kept.
    pattern = extract_gates(clauses)
    variants = []
    for name, base in (("highest-variable", pattern), ("fewest-occurrences", [g for g in pattern if g.kind not in ("xor2", "xor3")])):
        gs = base + extract_gates_generic(clauses, base)
        built = build_aig(nv, clauses, gs)
        variants.append((built[5], name, len(base), len(gs), built))
        print(f"  orientation {name}: {len(base)} by pattern + {len(gs) - len(base)} generic, {built[5]} on cycles", flush=True)
    variants.sort(key=lambda t: t[0])
    ncyclic, name, n_pattern, n_gates, built = variants[0]
    residual, pis, pos, ands, lit_of, ncyclic = built
    residual_units = [[l] for l in units]
    print(f"  orientation kept: {name}", flush=True)
    print(f"{os.path.basename(a.cnf)}: {nv} vars, {len(clauses)} clauses; {n_gates} gates ({ncyclic} on cycles), "
          f"AIG {len(pis)} inputs, {len(pos)} outputs, {len(ands)} ands; residual {len(residual)} clauses", flush=True)
    tmp = a.keep or tempfile.mkdtemp(prefix="cnf2aig_")
    os.makedirs(tmp, exist_ok=True)
    aag = a.aag or os.path.join(tmp, "in.aig")
    if aag.endswith(".aag"): write_aag(aag, pis, pos, ands, lit_of)
    else: write_aig(aag, pis, pos, ands, lit_of)
    if a.map:
        with open(a.map, "w") as f:
            f.write("pis " + " ".join(map(str, pis)) + "\n" + "pos " + " ".join(map(str, pos)) + "\n")
    if not a.out: return
    if a.abc and not ands:
        print("nothing to rewrite (no gates): the output is the input", flush=True)
        write_cnf(a.out, nv, [list(c) for c in clauses] + residual_units); return
    if not pos:
        # no gate output is mentioned outside its definition: the whole
        # circuit is dead logic, its definitions always satisfiable
        print("no observable gate output: the output is the residual", flush=True)
        write_cnf(a.out, nv, [list(clauses[i]) for i in residual] + residual_units); return
    if a.abc:
        script = SCRIPTS.get(a.script, a.script)
        rewritten = os.path.join(tmp, "out.aig"); abccnf = os.path.join(tmp, "out.abc.cnf"); gia = os.path.join(tmp, "out.gia.aig")
        steps = ["read_aiger " + aag, "strash"] + ([script, "strash"] if script else []) + ["write_aiger " + rewritten]
        if a.backend == "abc": steps += ["&get", "&w " + gia, "&write_cnf -i -o " + abccnf]
        r = subprocess.run([a.abc, "-q", "; ".join(steps)], capture_output=True, text=True)
        if r.returncode != 0 or not os.path.exists(rewritten):
            sys.exit(f"abc failed: {r.stdout[-500:]} {r.stderr[-500:]}")
        aig = read_aiger(rewritten)
        print(f"abc [{a.script}]: {aig[4]} ands ({len(ands)} before)", flush=True)
    else:
        aig = read_aiger(aag)
    if a.abc and a.backend == "abc":
        g = read_aiger(gia)
        assert g[1] == len(pis) and g[3] == len(pos), "the GIA's inputs/outputs do not match"
        nv2, cls = abc_cnf_to_cnf(nv, clauses, residual, pis, pos, abccnf, g[1], g[4])
    else:
        nv2, cls = aig_to_cnf(nv, clauses, residual, pis, pos, aig)
    cls += residual_units
    write_cnf(a.out, nv2, cls)
    print(f"-> {a.out}: {nv2} vars, {len(cls)} clauses", flush=True)

if __name__ == "__main__":
    main()
