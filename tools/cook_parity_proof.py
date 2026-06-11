#!/usr/bin/env python3
"""
Certified parity UNSAT: VeriPB proofs for GF(2) Gaussian-elimination
refutations, after Gocht & Nordstrom, "Certifying Parity Reasoning
Efficiently Using Pseudo-Boolean Proofs" (AAAI'21 / JAIR).

Pipeline:
  1. Recover XOR constraints from the CNF: a group of 2^(k-1) clauses over
     the same k variables, each excluding one wrong-parity assignment,
     encodes  x_1 ^ ... ^ x_k = b.
  2. GF(2) Gaussian elimination with provenance bitsets.  UNSAT iff some
     subset S of the recovered XORs sums to 0 = 1 (every variable appears
     an even number of times across S, but the parities sum odd).
  3. Emit, for each XOR in S (GN21 sections 4.1/4.4):
       - a chain of 1-bit full adders introduced by reification (`red`),
         deriving the PB equality  sum(x) = 2*sum(carries) + y'   (pol)
       - y' = b by brute force over assignments: 2^k `rup` clauses (each
         either subsumed by an original clause or propagation-refuted via
         the adder constraints) + a resolution tree (`pol ... 2 d`)
       - folds producing  GEQ: sum(x) - 2*sum(carries) >= b
                          LEQ: -sum(x) + 2*sum(carries) >= -b
  4. The contradiction (GN21 section 4.3 with the empty assignment): sum
     the GEQ of all of S — every x-coefficient is even, the RHS is odd —
     divide by 2 (rounds up), multiply by 2, add the summed LEQ: 0 >= 1.

Polynomial in the size of the clausal encoding.  Usage:
    cook_parity_proof.py <input.cnf> <out.pbp>
Verify:  veripb <input.cnf> <out.pbp>
"""
import sys
from collections import defaultdict


def parse_cnf(path):
    clauses, nvars = [], 0
    for ln in open(path):
        ln = ln.strip()
        if not ln or ln[0] in "pc%":
            continue
        lits = [int(x) for x in ln.split()]
        if lits and lits[-1] == 0:
            lits = lits[:-1]
        if lits:
            clauses.append(lits)
            nvars = max(nvars, max(abs(l) for l in lits))
    return nvars, clauses


def recover_xors(clauses):
    """Return a list of (vars_sorted, b, clause_ids) for every full XOR
    encoding present: 2^(k-1) clauses over the same k vars, all excluding
    assignments of the same (wrong) parity."""
    groups = defaultdict(list)
    for i, c in enumerate(clauses):
        vs = tuple(sorted(abs(l) for l in c))
        if len(vs) == len(set(vs)):            # no duplicate vars
            groups[vs].append(i)
    xors = []
    for vs, ids in groups.items():
        k = len(vs)
        if k < 2:
            continue
        # A clause (l1 v ... v lk) excludes the assignment x_i = 0 if l_i>0
        # else 1, whose parity is (#negative lits) mod 2.  An XOR with
        # parity b is the set of 2^(k-1) clauses excluding all parity-(1-b)
        # assignments.  Both parities can coexist over the SAME var set
        # (x^y=0 AND x^y=1), so partition the group by excluded parity.
        by_par = {0: set(), 1: set()}
        ok = True
        for ci in ids:
            c = clauses[ci]
            if sorted(abs(l) for l in c) != list(vs):
                ok = False
                break
            neg = sum(1 for l in c if l < 0)
            asg = tuple(sorted((abs(l), 0 if l > 0 else 1) for l in c))
            by_par[neg & 1].add(asg)
        if not ok:
            continue
        for par, excl in by_par.items():
            if len(excl) == 1 << (k - 1):
                xors.append((list(vs), 1 - par, ids))
    return xors


def ge_unsat_subset(nvars, xors):
    """GF(2) GE with provenance.  Returns the list of xor-indices whose sum
    is 0 = 1, or None if the system is consistent."""
    rows = []
    for i, (vs, b, _) in enumerate(xors):
        mask = 0
        for v in vs:
            mask |= 1 << v
        rows.append([mask, b, 1 << i])         # (var-bitset, rhs, provenance)
    pivots = {}
    for r in rows:
        mask, b, prov = r
        while mask:
            piv = mask.bit_length() - 1
            if piv in pivots:
                pm, pb, pp = pivots[piv]
                mask ^= pm
                b ^= pb
                prov ^= pp
            else:
                pivots[piv] = (mask, b, prov)
                break
        else:
            if b == 1:                          # 0 = 1
                return [i for i in range(len(xors)) if (prov >> i) & 1]
    return None


class Emit:
    def __init__(self, w, n_clauses):
        self.w = w
        self.id = n_clauses

    def line(self, s):
        self.w.write(s + "\n")

    def rule(self, s):
        self.w.write(s + "\n")
        self.id += 1
        return self.id


def lit(v, neg=False):
    return ("~x%d" % v) if neg else ("x%d" % v)


def emit_xor(e, vs, b, next_var):
    """Emit the GN21 machinery for one XOR (vars vs, parity b).  Fresh vars
    are allocated from next_var.  Returns (geq_id, leq_id, carries, next_var)
    where carries are the fresh carry vars (one per adder)."""
    k = len(vs)
    # --- adder chain: running parity z, carries ys, forced-zero pads ws.
    adders = []          # (in1, in2, in3, y, z) as signed "literal vars"
    ws = []
    ys = []
    chain = vs[0]
    rest = vs[1:]
    i = 0
    while i < len(rest):
        a = rest[i]
        if i + 1 < len(rest):
            bb = rest[i + 1]
            i += 2
        else:
            bb = next_var          # pad with a fresh forced-zero w
            ws.append(bb)
            next_var += 1
            i += 1
        y = next_var
        z = next_var + 1
        next_var += 2
        ys.append(y)
        adders.append((chain, a, bb, y, z))
        chain = z
    yp = chain                     # y' = final sum bit
    # --- forced-zero pads
    w_ids = {}
    for wv in ws:
        w_ids[wv] = e.rule("red +1 %s >= 1 : x%d -> 0 ;" % (lit(wv, True), wv))
    # --- reifications + adder equalities
    geq_ids, leq_ids = [], []
    for (a, bb, c, y, z) in adders:
        r_ypos = e.rule("red +2 %s +1 %s +1 %s +1 %s >= 2 : x%d -> 1 ;" %
                        (lit(y), lit(a, True), lit(bb, True), lit(c, True), y))
        r_yneg = e.rule("red +2 %s +1 %s +1 %s +1 %s >= 2 : x%d -> 0 ;" %
                        (lit(y, True), lit(a), lit(bb), lit(c), y))
        r_zpos = e.rule("red +3 %s +1 %s +1 %s +1 %s +2 %s >= 3 : x%d -> 1 ;" %
                        (lit(z), lit(a, True), lit(bb, True), lit(c, True), lit(y), z))
        r_zneg = e.rule("red +3 %s +1 %s +1 %s +1 %s +2 %s >= 3 : x%d -> 0 ;" %
                        (lit(z, True), lit(a), lit(bb), lit(c), lit(y, True), z))
        geq_ids.append(e.rule("pol %d %d 2 * + 3 d ;" % (r_zpos, r_ypos)))
        leq_ids.append(e.rule("pol %d %d 2 * + 3 d ;" % (r_zneg, r_yneg)))
    # --- step 2: y'(b) >= 1 by brute force + resolution tree
    # leaves[asg] = constraint id of clause  y'(b) v C_(not asg)
    ypb = lit(yp, b == 0)          # y' if b=1 else ~y'
    leaves = {}
    for m in range(1 << k):
        terms = ["+1 %s" % ypb]
        for j, v in enumerate(vs):
            on = (m >> j) & 1      # assignment x_v = on
            terms.append("+1 %s" % lit(v, neg=bool(on)))
        leaves[m] = e.rule("rup %s >= 1 ;" % " ".join(terms))
    # resolve out variables one by one
    cur = leaves
    for j in range(k - 1, -1, -1):
        nxt = {}
        for m, cid in cur.items():
            if (m >> j) & 1:
                continue
            cid2 = cur[m | (1 << j)]
            nxt[m] = e.rule("pol %d %d + 2 d ;" % (cid, cid2))
        cur = nxt
    ypb_id = cur[0]                # y'(b) >= 1
    # --- folds -> GEQ / LEQ for the whole XOR
    # GEQ: pol-sum of leq_ids (sum >= 2y+z sides) cancels intermediate z's;
    # then + y'(b)-unit (when b=1 removes ~y' ... ) and pad units.
    expr = str(leq_ids[0])
    for q in leq_ids[1:]:
        expr += " %d +" % q
    if b == 1:
        expr += " %d +" % ypb_id            # y' >= 1 cancels ~y'
    else:
        expr += " %s +" % lit(yp)           # axiom y' >= 0 cancels ~y'
    for wv in ws:
        expr += " %d +" % w_ids[wv]         # ~w >= 1 cancels each pad
    geq = e.rule("pol %s ;" % expr)
    expr = str(geq_ids[0])
    for q in geq_ids[1:]:
        expr += " %d +" % q
    if b == 1:
        expr += " %s +" % lit(yp, True)     # axiom ~y' >= 0 cancels y'
    else:
        expr += " %d +" % ypb_id            # ~y' >= 1 cancels y'
    for wv in ws:
        expr += " %s +" % lit(wv)           # axiom w >= 0 cancels ~w
    leq = e.rule("pol %s ;" % expr)
    return geq, leq, next_var


def gen_proof(w, nvars, clauses, xors, subset):
    e = Emit(w, len(clauses))
    e.line("pseudo-Boolean proof version 3.0")
    e.line("%% certified parity refutation (GN21): %d XOR(s) in the "
           "inconsistent subset" % len(subset))
    e.line("f %d;" % len(clauses))
    next_var = nvars + 1
    geqs, leqs = [], []
    for i in subset:
        vs, b, _ = xors[i]
        g, l, next_var = emit_xor(e, vs, b, next_var)
        geqs.append(g)
        leqs.append(l)
    # batched sums (avoid one giant pol line)
    def batch_sum(ids):
        cur = ids
        while len(cur) > 1:
            nxt = []
            for i in range(0, len(cur), 512):
                chunk = cur[i:i + 512]
                if len(chunk) == 1:
                    nxt.append(chunk[0])
                    continue
                expr = str(chunk[0]) + "".join(" %d +" % q for q in chunk[1:])
                nxt.append(e.rule("pol %s ;" % expr))
            cur = nxt
        return cur[0]
    gsum = batch_sum(geqs)
    lsum = batch_sum(leqs)
    e.rule("pol %d 2 d 2 * %d + ;" % (gsum, lsum))
    e.line("rup >= 1 ;")
    e.id += 1
    e.line("")
    e.line("output NONE;")
    e.line("conclusion UNSAT : -1;")
    e.line("end pseudo-Boolean proof;")


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(1)
    nvars, clauses = parse_cnf(sys.argv[1])
    xors = recover_xors(clauses)
    if not xors:
        print("no XOR constraints recovered")
        sys.exit(3)
    subset = ge_unsat_subset(nvars, xors)
    if subset is None:
        print("XOR system consistent (recovered %d XORs) — no parity refutation"
              % len(xors))
        sys.exit(3)
    print("recovered %d XOR(s); inconsistent subset of %d (arities %s)"
          % (len(xors), len(subset),
             sorted({len(xors[i][0]) for i in subset})))
    with open(sys.argv[2], "w") as w:
        gen_proof(w, nvars, clauses, xors, subset)
    print("wrote %s" % sys.argv[2])


if __name__ == "__main__":
    main()
