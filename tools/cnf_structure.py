#!/usr/bin/env python3
"""What box-shaped structure does a CNF carry?  Per instance: size, clause
lengths, Tseitin gate definitions (AND/OR of any width, XOR2/XOR3, MAJ3 —
and full adders = XOR3 + MAJ3 on the same inputs), and same-scope groups
(≥ 2 clauses over one variable set of ≤ 12 variables: a table constraint's
direct encoding looks like this).  Reads .cnf or .cnf.xz.

    tools/cnf_structure.py [--max-clauses N] file …      (one line per file)
"""
import argparse, collections, itertools, lzma, os, sys

def read_cnf(path, max_clauses):
    opener = lzma.open if path.endswith(".xz") else open
    clauses, nv = [], 0
    with opener(path, "rt", errors="replace") as f:
        for line in f:
            if not line or line[0] in "cp%":
                if line.startswith("p cnf"): nv = int(line.split()[2])
                continue
            lits = [int(x) for x in line.split()]
            if lits and lits[-1] == 0: lits = lits[:-1]
            if not lits: continue
            clauses.append(lits)
            if len(clauses) > max_clauses: return nv, clauses, True
    return nv, clauses, False

def scan(path, max_clauses):
    nv, clauses, truncated = read_cnf(path, max_clauses)
    m = len(clauses)
    lens = collections.Counter(min(len(c), 6) for c in clauses)
    binset = {frozenset(c) for c in clauses if len(c) == 2}
    by_scope = collections.defaultdict(list)
    for c in clauses: by_scope[frozenset(abs(l) for l in c)].append(frozenset(c))
    # AND/OR gates: a clause (o ∨ ¬a1 ∨ … ∨ ¬ak) with binaries (¬o ∨ ai) for every i
    and_gates, and_clauses = collections.Counter(), 0
    for c in clauses:
        if len(c) < 3: continue
        for o in c:
            if all(frozenset((-o, -l)) in binset for l in c if l != o):
                and_gates[min(len(c) - 1, 5)] += 1; and_clauses += len(c); break
    # parity and majority constraints from same-scope groups
    xor2 = xor3 = maj3 = 0; gate_in_groups = 0
    parity_scopes = {}
    for scope, group in by_scope.items():
        k, g = len(scope), len(group)
        if k == 3 and g >= 4 and len({len(c) for c in group}) == 1 and len(next(iter(group))) == 3:
            # 4 clauses forbidding one parity class = an XOR2 gate (o = a ⊕ b)
            signs = {tuple(sorted(c)) for c in group}
            pos_counts = {sum(1 for l in c if l > 0) % 2 for c in signs}
            if g == 4 and len(pos_counts) == 1: xor2 += 1; gate_in_groups += 4; parity_scopes[scope] = True
        if k == 4:
            tern = [c for c in group if len(c) == 3]; quad = [c for c in group if len(c) == 4]
            if len(quad) == 8 and len({sum(1 for l in c if l > 0) % 2 for c in quad}) == 1:
                xor3 += 1; gate_in_groups += 8; parity_scopes[scope] = True
            if len(tern) == 6:
                # majority: for the output o, clauses (¬a∨¬b∨o) for each input pair and (a∨b∨¬o)
                for o in scope:
                    ins = [v for v in scope if v != o]
                    need = set()
                    for a, b in itertools.combinations(ins, 2):
                        need.add(frozenset((-a, -b, o))); need.add(frozenset((a, b, -o)))
                    if need <= set(tern): maj3 += 1; gate_in_groups += 6; break
    # full adders: an XOR3 scope and a MAJ3 scope sharing three variables (the inputs)
    xor_scopes = [s for s in parity_scopes if len(s) == 4]
    maj_scopes = [s for s, g in by_scope.items() if len(s) == 4 and sum(1 for c in g if len(c) == 3) == 6]
    inputs_of_maj = collections.Counter()
    for s in maj_scopes:
        for o in s: inputs_of_maj[frozenset(s - {o})] += 1
    full_adders = sum(1 for s in xor_scopes if any(inputs_of_maj[frozenset(s - {o})] for o in s))
    # same-scope groups (≤ 12 vars, ≥ 2 clauses), excluding the gate patterns counted above
    grp_clauses = sum(len(g) for s, g in by_scope.items() if len(s) <= 12 and len(g) >= 2)
    return {
        "vars": nv, "clauses": m, "trunc": truncated,
        "len2": lens[2] / m, "len3": lens[3] / m, "len4+": (m - lens[1] - lens[2] - lens[3]) / m,
        "and2": and_gates[2], "and3+": sum(v for k, v in and_gates.items() if k >= 3),
        "xor2": xor2, "xor3": xor3, "maj3": maj3, "fa": full_adders,
        "gate%": 100 * (and_clauses + gate_in_groups) / m, "scope%": 100 * grp_clauses / m,
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+"); ap.add_argument("--max-clauses", type=int, default=2_000_000)
    ap.add_argument("--label", action="append", default=[], help="label=file prefix (printed instead of the file name)")
    args = ap.parse_args()
    print("label\tvars\tclauses\tlen2\tlen3\tlen4+\tand2\tand3+\txor2\txor3\tmaj3\tfulladd\tgate%\tscope%")
    for f in args.files:
        try: r = scan(f, args.max_clauses)
        except Exception as e: print(f"{os.path.basename(f)[:60]}\tERROR {e}"); continue
        name = os.path.basename(f)
        for lab in args.label:
            l, pre = lab.split("=", 1)
            if name.startswith(pre): name = l
        print(f"{name[:70]}\t{r['vars']}\t{r['clauses']}{'+' if r['trunc'] else ''}\t{r['len2']:.2f}\t{r['len3']:.2f}\t{r['len4+']:.2f}\t{r['and2']}\t{r['and3+']}\t{r['xor2']}\t{r['xor3']}\t{r['maj3']}\t{r['fa']}\t{r['gate%']:.0f}\t{r['scope%']:.0f}", flush=True)

if __name__ == "__main__":
    main()
