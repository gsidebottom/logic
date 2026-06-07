#!/usr/bin/env python3
"""
Cook-style cardinality UNSAT proof for "embedded pigeonhole" CNFs.

Generalizes the PHP / RoundRobin Cook proofs (tools/cook_php_proof.py,
tools/cook_rr_proof.py) to ANY CNF that contains an embedded pigeonhole:

  * P "pigeon" clauses: variable-disjoint, all-positive at-least-one
    clauses, each of the same arity S  (pigeon p picks >= 1 of S slots).
  * S "holes": for slot s, the set { var s of each pigeon } forms a
    COMPLETE pairwise-mutex clique (hole s holds <= 1 pigeon).
  * P > S  (more pigeons than holes -> UNSAT).

Such structure is resolution-hard (cardinality-from-pairwise-mutex wall)
but has a polynomial VeriPB proof via Cook's recursive at-most-1:

  Step 1: per hole, at-most-1 over its P pigeon-vars
            (base IH(3) = pol of 3 mutexes / 2; IH(k)=red witness->0).
          => ~x_{0,s}+...+~x_{P-1,s} >= P-1
  Step 2: sum the S hole-at-most-1's  => sum_{s,p} ~x_{p,s} >= S*(P-1)
  Step 3: sum the P pigeon clauses    => sum_{p,s}  x_{p,s} >= P
  Step 4: pol(2)+pol(3): since x+~x = P*S over all P*S vars,
            P*S >= S*(P-1)+P = P*S + (P-S)  => 0 >= P-S  => UNSAT.

Detected automatically from the CNF (no hand-coded family knowledge), so
the same generator covers MVRoundRobin and any other aligned
at-least-one + slot-clique instance.

Usage:
    cook_card_proof.py <input.cnf> <out.pbp>
Emits the VeriPB proof; verify with:  veripb <input.cnf> <out.pbp>
"""
import sys


def parse_cnf(path):
    clauses = []
    nvars = 0
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


def detect_embedded_pigeonhole(clauses):
    """Return (pigeons, holes, pigeon_id, mutex_id) or raise ValueError.

    pigeons[p]  = sorted var list of pigeon p (the at-least-one clause)
    holes[s]    = [pigeons[p][s] for p]  (the s-th slot clique vars)
    pigeon_id[p]= 1-based clause id of pigeon p's at-least-one clause
    mutex_id[(a,b)] = 1-based clause id of the binary mutex on vars a<b
    """
    # All-positive at-least-one clauses of arity >= 2 are pigeon candidates.
    pigeons, pigeon_id = [], {}
    arity = None
    for i, c in enumerate(clauses):
        if len(c) >= 2 and all(l > 0 for l in c):
            if arity is None:
                arity = len(c)
            if len(c) == arity:
                pigeon_id[len(pigeons)] = i + 1
                pigeons.append(sorted(c))
    if len(pigeons) < 2:
        raise ValueError("no at-least-one pigeon family found")
    S = arity
    P = len(pigeons)
    # Pigeons must be variable-disjoint.
    seen = set()
    for g in pigeons:
        if any(v in seen for v in g):
            raise ValueError("pigeon clauses are not variable-disjoint")
        seen.update(g)
    if P <= S:
        raise ValueError(f"not a pigeonhole: {P} pigeons <= {S} holes")
    # Binary all-negative mutex index.
    mutex_id = {}
    for i, c in enumerate(clauses):
        if len(c) == 2 and c[0] < 0 and c[1] < 0:
            a, b = sorted((-c[0], -c[1]))
            mutex_id.setdefault((a, b), i + 1)
    # Holes = aligned slot cliques; require completeness.
    holes = []
    for s in range(S):
        hv = [pigeons[p][s] for p in range(P)]
        for ai in range(P):
            for bi in range(ai + 1, P):
                a, b = sorted((hv[ai], hv[bi]))
                if (a, b) not in mutex_id:
                    raise ValueError(
                        f"hole {s} clique incomplete: missing mutex "
                        f"({a},{b})")
        holes.append(hv)
    return pigeons, holes, pigeon_id, mutex_id


def gen_proof(nclauses, pigeons, holes, pigeon_id, mutex_id):
    P, S = len(pigeons), len(holes)
    lines = [
        "pseudo-Boolean proof version 3.0",
        f"% embedded pigeonhole: {P} pigeons > {S} holes (Cook cardinality)",
        f"f {nclauses};",
        "",
    ]
    cur = nclauses

    # Step 1: per-hole at-most-1 over the P pigeon-vars (Cook recursive).
    lines.append(f"% --- Step 1: per-hole at-most-1 over {P} vars (recursive Cook subroutine) ---")
    hole_amo = []
    for s in range(S):
        hv = holes[s]
        negs = [f"~x{v}" for v in hv]
        # base IH(3): pol of mutex(0,1),(0,2),(1,2) / 2 -> ~v0+~v1+~v2 >= 2
        m01 = mutex_id[tuple(sorted((hv[0], hv[1])))]
        m02 = mutex_id[tuple(sorted((hv[0], hv[2])))]
        m12 = mutex_id[tuple(sorted((hv[1], hv[2])))]
        lines.append(f"pol {m01} {m02} + {m12} + 2 d ;")
        cur += 1
        # IH(k) for k=4..P via recursive red: witness = k-th var -> 0
        for k in range(4, P + 1):
            amo = " ".join(f"+1 {negs[i]}" for i in range(k))
            lines.append(f"red {amo} >= {k - 1} : x{hv[k - 1]} -> 0 ;")
            cur += 1
        hole_amo.append(cur)  # constraint: sum_p ~x_{p,s} >= P-1
    lines.append("")

    # Step 2: sum the S hole-at-most-1's -> sum_{s,p} ~x >= S*(P-1)
    lines.append("% --- Step 2: sum hole at-most-1's ---")
    expr = f"{hole_amo[0]}"
    for hid in hole_amo[1:]:
        expr += f" {hid} +"
    lines.append(f"pol {expr} ;")
    cur += 1
    amo_sum = cur
    lines.append("")

    # Step 3: sum the P pigeon clauses -> sum_{p,s} x >= P
    lines.append("% --- Step 3: sum pigeon at-least-one clauses ---")
    expr = f"{pigeon_id[0]}"
    for p in range(1, P):
        expr += f" {pigeon_id[p]} +"
    lines.append(f"pol {expr} ;")
    cur += 1
    pigeon_sum = cur
    lines.append("")

    # Step 4: combine -> contradiction (x + ~x = P*S < S*(P-1)+P).
    lines.append("% --- Step 4: combine -> contradiction ---")
    lines.append(f"pol {amo_sum} {pigeon_sum} + ;")
    cur += 1
    lines.append("rup >= 1 ;")
    lines.append("")
    lines.append("output NONE;")
    lines.append("conclusion UNSAT : -1;")
    lines.append("end pseudo-Boolean proof;")
    return lines


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(1)
    cnf_path, out_path = sys.argv[1], sys.argv[2]
    nvars, clauses = parse_cnf(cnf_path)
    pigeons, holes, pigeon_id, mutex_id = detect_embedded_pigeonhole(clauses)
    P, S = len(pigeons), len(holes)
    print(f"detected embedded pigeonhole: {P} pigeons, {S} holes "
          f"({nvars} vars, {len(clauses)} clauses)")
    lines = gen_proof(len(clauses), pigeons, holes, pigeon_id, mutex_id)
    with open(out_path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote {out_path}: {len(lines)} proof lines")


if __name__ == "__main__":
    main()
