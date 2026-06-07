#!/usr/bin/env python3
"""
Two-level Cook PB proof for clique-coloring CNFs (VeriPB-checkable).

A clique-coloring formula asserts a graph contains a K-clique (via K
"clique-slot" selector clauses) yet is C-colorable, with K > C — UNSAT
because the K mutually-adjacent clique vertices need K distinct colors.
This is a pigeonhole at the COMPOSED clique-slot -> color level, so the
proof composes the two cardinality layers (clique membership + coloring):

  z_{i,v,c} = clique_{i,v} AND col_{v,c}     (AND reification via red)
  y_{i,c}   = OR_v z_{i,v,c}                  (OR  reification via red)
  (A) OR_c y_{i,c}  per slot i               (composed at-least-one)
  (B) ~y_{i,c} | ~y_{j,c}  per color, i<j    (composed at-most-1)
  PHP-K-C on y                               -> contradiction

(A)/(B) are derived with `rup` plus intermediate lemmas that make unit
propagation cascade through the existential composition:
  (A): T = ~clique_{i,v} | ~col_{v,c} | y_{i,c};  U = ~clique_{i,v} | OR_c y.
  (B): N = ~z_{i,v,c} | ~z_{j,w,c};  Q = ~z_{i,v,c} | ~y_{j,c}.

Structure is read directly from the CNF: the K largest-arity all-positive
clauses are clique-membership (arity = #vertices N), the N next all-
positive clauses are vertex-color (arity = #colors C); clique-clause i's
v-th sorted var is clique_{i,v}, the v-th color-clause is vertex v.

Usage:  cook_cliquecoloring_proof.py <input.cnf> <out.pbp>
Verify: veripb <input.cnf> <out.pbp>
"""
import sys
from collections import defaultdict


def parse_cnf(path):
    clauses, nv = [], 0
    for ln in open(path):
        ln = ln.strip()
        if not ln or ln[0] in "pc%":
            continue
        lits = [int(x) for x in ln.split()]
        if lits and lits[-1] == 0:
            lits = lits[:-1]
        if lits:
            clauses.append(lits)
            nv = max(nv, max(abs(l) for l in lits))
    return nv, clauses


def detect(clauses):
    """Return (clique, color) where clique[i] = sorted vars of clique-slot
    i (length N), color[v] = sorted vars of vertex v (length C), aligned so
    clique[i][v] and color[v] refer to the same vertex v."""
    pos = defaultdict(list)
    for c in clauses:
        if len(c) >= 2 and all(l > 0 for l in c):
            pos[len(c)].append(sorted(c))
    if len(pos) < 2:
        raise ValueError("need >=2 all-positive arities (clique + color)")
    arities = sorted(pos)
    n_arity = arities[-1]          # clique-membership arity = #vertices N
    c_arity = arities[-2]          # vertex-color arity = #colors C
    clique = pos[n_arity]
    color = pos[c_arity]
    K, N, C = len(clique), n_arity, c_arity
    if len(color) != N:
        raise ValueError("vertex-color count %d != #vertices %d" % (len(color), N))
    if K <= C:
        raise ValueError("not UNSAT clique-coloring: K=%d <= C=%d" % (K, C))
    # Order color-clauses by vertex (their min var ascends with vertex id).
    color = sorted(color, key=lambda cl: cl[0])
    return clique, color


def gen(cnf_path, out_path):
    nv, clauses = parse_cnf(cnf_path)
    clique, color = detect(clauses)
    K, N, C = len(clique), len(clique[0]), len(color[0])
    Q = clique[0][0]  # silence linters; not used

    def cl(i, v):
        return clique[i][v]        # clique_{i,v}

    def co(v, cc):
        return color[v][cc]        # col_{v,cc}

    nxt = nv
    z = {}
    for i in range(K):
        for v in range(N):
            for cc in range(C):
                nxt += 1
                z[(i, v, cc)] = nxt
    y = {}
    for i in range(K):
        for cc in range(C):
            nxt += 1
            y[(i, cc)] = nxt

    L = ["pseudo-Boolean proof version 3.0",
         "%% clique-coloring two-level: composed PHP-%d-%d (slot->color)" % (K, C),
         "f %d;" % len(clauses), ""]
    cur = [len(clauses)]

    def step(s):
        L.append(s)
        cur[0] += 1
        return cur[0]

    # z = clique AND col
    for i in range(K):
        for v in range(N):
            for cc in range(C):
                zz = z[(i, v, cc)]
                step("red 1 ~x%d 1 x%d >= 1 : x%d -> 0 ;" % (zz, cl(i, v), zz))
                step("red 1 ~x%d 1 x%d >= 1 : x%d -> 0 ;" % (zz, co(v, cc), zz))
                step("red 1 x%d 1 ~x%d 1 ~x%d >= 1 : x%d -> 1 ;" % (zz, cl(i, v), co(v, cc), zz))
    # y = OR_v z
    for i in range(K):
        for cc in range(C):
            yy = y[(i, cc)]
            for v in range(N):
                step("red 1 ~x%d 1 x%d >= 1 : x%d -> 1 ;" % (z[(i, v, cc)], yy, yy))
            terms = " ".join("1 x%d" % z[(i, v, cc)] for v in range(N))
            step("red 1 ~x%d %s >= 1 : x%d -> 0 ;" % (yy, terms, yy))
    # (A) composed at-least-one
    A = {}
    for i in range(K):
        for v in range(N):
            for cc in range(C):
                step("rup 1 ~x%d 1 ~x%d 1 x%d >= 1 ;" % (cl(i, v), co(v, cc), y[(i, cc)]))
        for v in range(N):
            terms = " ".join("1 x%d" % y[(i, cc)] for cc in range(C))
            step("rup 1 ~x%d %s >= 1 ;" % (cl(i, v), terms))
        terms = " ".join("1 x%d" % y[(i, cc)] for cc in range(C))
        A[i] = step("rup %s >= 1 ;" % terms)
    # (B) composed at-most-1
    B = {}
    for cc in range(C):
        for i in range(K):
            for j in range(i + 1, K):
                for v in range(N):
                    for w in range(N):
                        step("rup 1 ~x%d 1 ~x%d >= 1 ;" % (z[(i, v, cc)], z[(j, w, cc)]))
                for v in range(N):
                    step("rup 1 ~x%d 1 ~x%d >= 1 ;" % (z[(i, v, cc)], y[(j, cc)]))
                B[(i, j, cc)] = step("rup 1 ~x%d 1 ~x%d >= 1 ;" % (y[(i, cc)], y[(j, cc)]))
    # PHP-K-C on y
    hole_amo = []
    for cc in range(C):
        ys = [y[(i, cc)] for i in range(K)]
        cid = step("pol %d %d + %d + 2 d ;" % (B[(0, 1, cc)], B[(0, 2, cc)], B[(1, 2, cc)]))
        for kk in range(4, K + 1):
            lits = " ".join("1 ~x%d" % ys[t] for t in range(kk))
            cid = step("red %s >= %d : x%d -> 0 ;" % (lits, kk - 1, ys[kk - 1]))
        hole_amo.append(cid)
    expr = "%d" % hole_amo[0] + "".join(" %d +" % h for h in hole_amo[1:])
    amo_sum = step("pol %s ;" % expr)
    expr = "%d" % A[0] + "".join(" %d +" % A[i] for i in range(1, K))
    pig_sum = step("pol %s ;" % expr)
    step("pol %d %d + ;" % (amo_sum, pig_sum))
    L += ["rup >= 1 ;", "output NONE;", "conclusion UNSAT : -1;",
          "end pseudo-Boolean proof;"]
    open(out_path, "w").write("\n".join(L) + "\n")
    print("clique-coloring K=%d N=%d C=%d: %d proof lines, %d ext vars"
          % (K, N, C, len(L), nxt - nv))


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(1)
    gen(sys.argv[1], sys.argv[2])
