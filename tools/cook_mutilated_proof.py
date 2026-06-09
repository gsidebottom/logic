#!/usr/bin/env python3
"""
Cook-style cardinality UNSAT proof for the MUTILATED CHESSBOARD and, more
generally, any bipartite perfect-matching infeasibility caused by a side
imbalance.

Structure detected (perfect-matching / domino-tiling encoding):
  * "square" clauses: all-positive at-least-one clauses S_v = (e1 v e2 v ...),
    one per square v, over the domino-edge variables incident to v.
  * each edge variable occurs in exactly TWO square clauses (its endpoints).
  * per square, the incident edges are pairwise-mutex (binary ~ei v ~ej) —
    i.e. at-most-one domino per square; together with the at-least-one this
    is an exactly-one (perfect matching).
  * the square-adjacency graph (squares sharing an edge) is BIPARTITE; the
    two sides have different sizes W > B (mutilated chessboard: removing two
    same-colour corners leaves 143 vs 144).  => no perfect matching => UNSAT.
  * optional negative units ~e force the edges of removed squares off.

Resolution-hard (Alekhnovich 2004: mutilated chessboard is exponential for
resolution) but a one-shot cutting-planes argument:
  Step 1: per minority square, at-most-1 over its incident edges
          (recursive Cook: base IH(3)=pol of 3 mutexes/2, IH(k)=red).
          => sum_{e in B} ~e >= deg - 1  per square
  Step 2: sum the minority at-most-1's   => sum_e ~e >= E - B
  Step 3: sum the majority at-least-1's   => sum_e e >= W   (+ forced edges)
  Step 4: combine: each edge is one majority + one minority endpoint, so
          e + ~e cancel to E; left with (forced edges) >= W - B; add the
          forced-off units => W - B <= 0, contradicting W > B.  UNSAT.

Usage:    cook_mutilated_proof.py <input.cnf> <out.pbp>
Verify:   veripb <input.cnf> <out.pbp>
"""
import sys
from collections import defaultdict, deque


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


def _neg(l):
    """VeriPB term for the literal being false."""
    return "~x%d" % l if l > 0 else "x%d" % (-l)


def detect(clauses):
    """Return a dict describing the bipartite-matching structure, or raise."""
    # square clauses = all-positive, arity >= 2; remember 1-based clause ids.
    squares, sq_id = [], []
    units = []                                   # forced-off edges (~e units)
    mutex_id = {}                                # (a,b) -> id of (~a v ~b)
    for i, c in enumerate(clauses):
        cid = i + 1
        if len(c) == 1 and c[0] < 0:
            units.append(-c[0])
        elif len(c) >= 2 and all(x > 0 for x in c):
            squares.append(sorted(c)); sq_id.append(cid)
        elif len(c) == 2 and all(x < 0 for x in c):
            a, b = -c[0], -c[1]
            mutex_id[(min(a, b), max(a, b))] = cid
    if len(squares) < 4:
        raise ValueError("no square (at-least-one) clauses")
    # edge -> list of square indices it occurs in (must be exactly 2 for a
    # genuine edge; edges to removed squares may occur in 1 and be unit-forced).
    occ = defaultdict(list)
    for si, c in enumerate(squares):
        for v in c:
            occ[v].append(si)
    forced = set(units)
    # adjacency over squares sharing a (non-forced) edge in exactly 2 squares
    adj = defaultdict(set)
    for v, sqs in occ.items():
        if v in forced:
            continue
        if len(sqs) != 2:
            raise ValueError("edge %d in %d squares (need 2)" % (v, len(sqs)))
        a, b = sqs
        adj[a].add(b); adj[b].add(a)
    # 2-colour the square graph
    color = {}
    for s in range(len(squares)):
        if s in color:
            continue
        color[s] = 0
        q = deque([s])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if w not in color:
                    color[w] = color[u] ^ 1; q.append(w)
                elif color[w] == color[u]:
                    raise ValueError("square graph not bipartite")
    side = {0: [], 1: []}
    for s in range(len(squares)):
        side[color.get(s, 0)].append(s)
    W, B = len(side[0]), len(side[1])
    if W == B:
        raise ValueError("balanced bipartition (W==B): not an imbalance refutation")
    maj, mino = (0, 1) if W > B else (1, 0)      # majority colour index
    # every minority square's incident edges must be pairwise-mutex (at-most-1)
    for s in side[mino]:
        c = squares[s]
        for i in range(len(c)):
            for j in range(i + 1, len(c)):
                if (c[i], c[j]) not in mutex_id:
                    raise ValueError("minority square %d missing mutex (%d,%d)"
                                     % (s, c[i], c[j]))
    return dict(squares=squares, sq_id=sq_id, side=side, maj=maj, mino=mino,
                W=max(W, B), B=min(W, B), forced=forced, mutex_id=mutex_id,
                unit_id={u: i + 1 for i, c in enumerate(clauses)
                         for u in ([-c[0]] if len(c) == 1 and c[0] < 0 else [])})


def gen_proof(nclauses, d):
    squares, sq_id = d["squares"], d["sq_id"]
    side, maj, mino = d["side"], d["maj"], d["mino"]
    forced, mutex_id, unit_id = d["forced"], d["mutex_id"], d["unit_id"]
    W, B = d["W"], d["B"]
    L = ["pseudo-Boolean proof version 3.0",
         "%% mutilated chessboard / bipartite matching: %d > %d  (imbalance %d)"
         % (W, B, W - B),
         "f %d;" % nclauses, ""]
    cur = nclauses

    # --- Step 1+2: minority at-most-1's, summed ---
    L.append("%% --- per-minority-square at-most-1 (active edges) ---")
    amo_ids = []
    for s in side[mino]:
        edges = [e for e in squares[s] if e not in forced]
        k = len(edges)
        if k < 2:
            continue
        if k == 2:                               # the mutex IS the at-most-1
            amo_ids.append(mutex_id[(edges[0], edges[1])]); continue
        m01 = mutex_id[(edges[0], edges[1])]
        m02 = mutex_id[(edges[0], edges[2])]
        m12 = mutex_id[(edges[1], edges[2])]
        L.append("pol %d %d + %d + 2 d ;" % (m01, m02, m12))   # IH(3)
        cur += 1
        for j in range(4, k + 1):                # IH(4..k) via red witness
            amo = " ".join("+1 %s" % _neg(edges[i]) for i in range(j))
            wl = edges[j - 1]
            L.append("red %s >= %d : x%d -> %d ;" % (amo, j - 1, wl, 0))
            cur += 1
        amo_ids.append(cur)
    L.append("")
    L.append("%% --- sum minority at-most-1's => sum ~e >= E - B ---")
    L.append("pol %s ;" % (str(amo_ids[0]) + "".join(" %d +" % a for a in amo_ids[1:])))
    cur += 1
    min_sum = cur

    # --- Step 3: majority at-least-1's (original clauses), summed ---
    L.append("")
    L.append("%% --- sum majority at-least-1 clauses => sum e >= W ---")
    maj_ids = [sq_id[s] for s in side[maj]]
    L.append("pol %s ;" % (str(maj_ids[0]) + "".join(" %d +" % a for a in maj_ids[1:])))
    cur += 1
    maj_sum = cur

    # --- Step 4: combine + cancel forced edges with their units ---
    L.append("")
    L.append("%% --- combine: each edge is one majority + one minority => cancel;")
    L.append("%%     forced-off edges left over are killed by their units ---")
    comb = "%d %d +" % (maj_sum, min_sum)
    for e in sorted(forced):
        if e in unit_id:
            comb += " %d +" % unit_id[e]
    L.append("pol %s ;" % comb)
    cur += 1
    L += ["rup >= 1 ;", "", "output NONE;",
          "conclusion UNSAT : -1;", "end pseudo-Boolean proof;"]
    return L


def main():
    if len(sys.argv) != 3:
        print(__doc__); sys.exit(1)
    cnf_path, out_path = sys.argv[1], sys.argv[2]
    nvars, clauses = parse_cnf(cnf_path)
    d = detect(clauses)
    print("detected mutilated chessboard: %d majority squares > %d minority, "
          "%d forced-off edges (%d vars, %d clauses)"
          % (d["W"], d["B"], len(d["forced"]), nvars, len(clauses)))
    lines = gen_proof(len(clauses), d)
    with open(out_path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print("wrote %s: %d proof lines" % (out_path, len(lines)))


if __name__ == "__main__":
    main()
