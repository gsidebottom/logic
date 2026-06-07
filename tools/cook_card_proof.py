#!/usr/bin/env python3
"""
Cook-style cardinality UNSAT proof for "embedded pigeonhole" CNFs.

Generalizes the PHP / RoundRobin Cook proofs (tools/cook_php_proof.py,
tools/cook_rr_proof.py) to ANY CNF that contains an embedded pigeonhole,
including reshuffled / polarity-flipped encodings (e.g. harder-fphp):

  * P "pigeon" clauses: variable-disjoint at-least-one clauses of equal
    arity S, with literals of ANY polarity (l_{p,s} = "pigeon p in hole
    s", possibly negated).
  * S "holes": for each hole the P pigeon-literals form a COMPLETE
    pairwise-mutex clique (hole holds <= 1 pigeon).  Holes are recovered
    two ways, tried in order:
      (A) component:  connected components of the cross-pigeon mutex graph
                      (works for PHP / reshuffled fphp).
      (B) aligned:    the s-th literal of each pigeon, sorted by |var|
                      (works for MVRoundRobin, whose extra team-capacity
                      mutexes merge the component graph).
  * P > S  (more pigeons than holes -> UNSAT).

Resolution-hard (cardinality-from-pairwise-mutex wall) but has a
polynomial VeriPB proof via Cook's recursive at-most-1, emitted at the
LITERAL level so flipped polarities are handled transparently:

  Step 1: per hole, at-most-1 over its P pigeon-literals
            (base IH(3)=pol of 3 mutexes/2; IH(k)=red witness->{0,1}).
          => sum ~l_{*,s} >= P-1
  Step 2: sum the S holes        => sum_{s,p} ~l >= S*(P-1)
  Step 3: sum the P pigeons      => sum_{p,s}  l >= P
  Step 4: l + ~l = P*S over all P*S literals, so
            P*S >= S*(P-1)+P = P*S + (P-S)  => 0 >= P-S  => UNSAT.

Usage:
    cook_card_proof.py <input.cnf> <out.pbp>
Verify with:  veripb <input.cnf> <out.pbp>
"""
import sys
from collections import Counter, defaultdict


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


def _valid_holes(holes, P):
    """Holes are valid iff there are >=1, each has exactly P literals
    (one per pigeon — guaranteed by construction), and P > #holes."""
    return holes is not None and len(holes) >= 1 and P > len(holes)


def _recover_component(pigeons, lit2pig, mutex):
    """Holes = connected components of the cross-pigeon mutex graph;
    each must be a complete P-clique with one literal per pigeon."""
    adj = defaultdict(set)
    for (la, lb) in mutex:
        if la in lit2pig and lb in lit2pig and lit2pig[la] != lit2pig[lb]:
            adj[la].add(lb)
            adj[lb].add(la)
    P = len(pigeons)
    seen, holes = set(), []
    for lit in lit2pig:
        if lit in seen:
            continue
        stack, comp = [lit], []
        while stack:
            u = stack.pop()
            if u in seen:
                continue
            seen.add(u)
            comp.append(u)
            stack.extend(adj[u] - seen)
        holes.append(comp)
    out = []
    for comp in holes:
        if len(comp) != P:
            return None
        if len({lit2pig[l] for l in comp}) != P:
            return None
        # complete clique?
        for i in range(len(comp)):
            for j in range(i + 1, len(comp)):
                if comp[j] not in adj[comp[i]]:
                    return None
        out.append(sorted(comp, key=lambda l: lit2pig[l]))
    return out


def _recover_aligned(pigeons, mutex):
    """Holes = s-th literal of each pigeon (sorted by |var|); each slot
    must be a complete pairwise-mutex clique."""
    P, S = len(pigeons), len(pigeons[0])
    pigs = [sorted(g, key=abs) for g in pigeons]
    holes = []
    for s in range(S):
        hv = [pigs[p][s] for p in range(P)]
        for i in range(P):
            for j in range(i + 1, P):
                if tuple(sorted((hv[i], hv[j]))) not in mutex:
                    return None
        holes.append(hv)
    return holes


def detect_embedded_pigeonhole(clauses):
    """Return (pigeons, holes, pigeon_ids, mutex_id) or raise ValueError.

    pigeons[p] = signed-literal list of pigeon p's at-least-one clause.
    holes[s]   = the P pigeon-literals forming hole s (pigeon order).
    pigeon_ids = 1-based clause id per pigeon.
    mutex_id[(la,lb)] = 1-based clause id of the binary clause excluding
                        the literal pair (la, lb)  (i.e. ~la v ~lb).
    """
    # Pigeons: disjoint clauses sharing the first all-arity seen, arity>=2.
    arity = 0
    pigeons, pigeon_ids = [], []
    for i, c in enumerate(clauses):
        if len(c) >= 2:
            if arity == 0 and len(c) >= 3:
                arity = len(c)
            if arity and len(c) == arity:
                pigeons.append(list(c))
                pigeon_ids.append(i + 1)
    P, S = len(pigeons), arity
    if P < 3 or S < 2 or P <= S:
        raise ValueError(f"no pigeonhole shape ({P} pigeons, {S} holes)")
    seen = set()
    lit2pig = {}
    for pi, g in enumerate(pigeons):
        for l in g:
            if abs(l) in seen:
                raise ValueError("pigeon clauses not variable-disjoint")
            seen.add(abs(l))
            lit2pig[l] = pi
    # Binary mutex index, keyed on the EXCLUDED literal pair (~la v ~lb).
    mutex_id = {}
    for i, c in enumerate(clauses):
        if len(c) == 2:
            la, lb = -c[0], -c[1]
            mutex_id[tuple(sorted((la, lb)))] = i + 1
    mutex = set(mutex_id)
    holes = _recover_component(pigeons, lit2pig, mutex)
    if not _valid_holes(holes, P):
        holes = _recover_aligned(pigeons, mutex)
    if not _valid_holes(holes, P):
        raise ValueError("could not recover complete hole cliques")
    return pigeons, holes, pigeon_ids, mutex_id


def _neg(l):
    """The VeriPB term for ~l (the literal being false)."""
    return f"~x{l}" if l > 0 else f"x{-l}"


def gen_proof(nclauses, pigeons, holes, pigeon_ids, mutex_id):
    P, S = len(pigeons), len(holes)
    lines = [
        "pseudo-Boolean proof version 3.0",
        f"% embedded pigeonhole: {P} pigeons > {S} holes (literal-level Cook)",
        f"f {nclauses};",
        "",
        f"% --- Step 1: per-hole at-most-1 over {P} literals (recursive Cook) ---",
    ]
    cur = nclauses
    hole_amo = []
    for hv in holes:
        m01 = mutex_id[tuple(sorted((hv[0], hv[1])))]
        m02 = mutex_id[tuple(sorted((hv[0], hv[2])))]
        m12 = mutex_id[tuple(sorted((hv[1], hv[2])))]
        lines.append(f"pol {m01} {m02} + {m12} + 2 d ;")
        cur += 1
        for k in range(4, P + 1):
            amo = " ".join(f"+1 {_neg(hv[i])}" for i in range(k))
            wl = hv[k - 1]
            lines.append(f"red {amo} >= {k - 1} : x{abs(wl)} -> {0 if wl > 0 else 1} ;")
            cur += 1
        hole_amo.append(cur)
    lines.append("")
    lines.append("% --- Step 2: sum hole at-most-1's ---")
    expr = f"{hole_amo[0]}" + "".join(f" {h} +" for h in hole_amo[1:])
    lines.append(f"pol {expr} ;")
    cur += 1
    amo_sum = cur
    lines.append("")
    lines.append("% --- Step 3: sum pigeon at-least-one clauses ---")
    expr = f"{pigeon_ids[0]}" + "".join(f" {p} +" for p in pigeon_ids[1:])
    lines.append(f"pol {expr} ;")
    cur += 1
    pigeon_sum = cur
    lines.append("")
    lines.append("% --- Step 4: combine -> contradiction ---")
    lines.append(f"pol {amo_sum} {pigeon_sum} + ;")
    cur += 1
    lines += ["rup >= 1 ;", "", "output NONE;",
              "conclusion UNSAT : -1;", "end pseudo-Boolean proof;"]
    return lines


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(1)
    cnf_path, out_path = sys.argv[1], sys.argv[2]
    nvars, clauses = parse_cnf(cnf_path)
    pigeons, holes, pigeon_ids, mutex_id = detect_embedded_pigeonhole(clauses)
    print(f"detected embedded pigeonhole: {len(pigeons)} pigeons, "
          f"{len(holes)} holes ({nvars} vars, {len(clauses)} clauses)")
    lines = gen_proof(len(clauses), pigeons, holes, pigeon_ids, mutex_id)
    with open(out_path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote {out_path}: {len(lines)} proof lines")


if __name__ == "__main__":
    main()
