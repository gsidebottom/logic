#!/usr/bin/env python3
"""
DIMACS CNF -> NeuroSAT-style literal–clause bipartite graph.

The representation (Selsam et al., NeuroSAT, ICLR 2019; the encoder
NeuroBack/SAT-GATv2 also build on):

  * 2*nvars LITERAL nodes.  Literal l (l != 0, v = |l|) maps to node
        lit_node(l) = 2*(v-1) + (0 if l > 0 else 1)
    so var v's positive literal is node 2(v-1), its negative 2(v-1)+1.
  * nclauses CLAUSE nodes, 0..nclauses-1.
  * an undirected edge {literal node, clause node} for each literal
    occurrence — message passing runs over these.
  * a `flip` permutation pairing each literal node with its complement
    (NeuroSAT's L_flip), so the network can relate x and ¬x.

Everything is numpy + COO edge arrays — framework-agnostic, GPU-free; the
MLX GNN (model.py) consumes these directly.  Per-VARIABLE outputs (e.g.
the phase-prediction head) aggregate a variable's two literal nodes.

Usage:  sat_graph.py <input.cnf[.xz]>      # prints graph stats
"""
from __future__ import annotations

import sys
import lzma
from dataclasses import dataclass

import numpy as np


def parse_dimacs(path: str) -> tuple[int, list[list[int]]]:
    """Parse a DIMACS CNF (plain or .xz).  Returns (nvars, clauses) where
    each clause is a list of nonzero ints.  Robust to clauses spanning
    lines and a missing/loose header (nvars taken from the literals)."""
    opener = lzma.open if path.endswith(".xz") else open
    clauses: list[list[int]] = []
    cur: list[int] = []
    nvars = 0
    with opener(path, "rt") as f:
        for line in f:
            s = line.strip()
            if not s or s[0] in "pc%":
                continue
            for tok in s.split():
                v = int(tok)
                if v == 0:
                    if cur:
                        clauses.append(cur)
                        cur = []
                else:
                    cur.append(v)
                    if abs(v) > nvars:
                        nvars = abs(v)
    if cur:
        clauses.append(cur)
    return nvars, clauses


@dataclass
class SatGraph:
    n_vars: int
    n_clauses: int
    n_lit_nodes: int            # == 2 * n_vars
    edge_lit: np.ndarray        # COO: literal-node endpoints (int32)
    edge_clause: np.ndarray     # COO: clause-node endpoints (int32), aligned
    flip: np.ndarray            # literal-node -> complement-node permutation

    @property
    def n_edges(self) -> int:
        return int(self.edge_lit.shape[0])

    def var_lit_nodes(self, v: int) -> tuple[int, int]:
        """(positive, negative) literal-node indices for 1-based var v."""
        return 2 * (v - 1), 2 * (v - 1) + 1


def lit_node(lit: int) -> int:
    """Literal-node index for a nonzero DIMACS literal."""
    v = abs(lit)
    return 2 * (v - 1) + (0 if lit > 0 else 1)


def build_graph(clauses: list[list[int]], nvars: int) -> SatGraph:
    """Build the literal–clause bipartite graph from parsed clauses."""
    n_lit = 2 * nvars
    lit_ep: list[int] = []
    cls_ep: list[int] = []
    for ci, clause in enumerate(clauses):
        for lit in clause:
            lit_ep.append(lit_node(lit))
            cls_ep.append(ci)
    # flip[2i] = 2i+1, flip[2i+1] = 2i  (pos <-> neg literal of each var)
    flip = np.arange(n_lit, dtype=np.int32)
    flip[0::2] += 1
    flip[1::2] -= 1
    return SatGraph(
        n_vars=nvars,
        n_clauses=len(clauses),
        n_lit_nodes=n_lit,
        edge_lit=np.asarray(lit_ep, dtype=np.int32),
        edge_clause=np.asarray(cls_ep, dtype=np.int32),
        flip=flip,
    )


def from_file(path: str) -> SatGraph:
    nvars, clauses = parse_dimacs(path)
    return build_graph(clauses, nvars)


# ─── self-test ──────────────────────────────────────────────────────────────

def _selftest() -> None:
    # (x1 v x2 v ~x3) ^ (~x1 v x3) ^ (x2)   over 3 vars
    clauses = [[1, 2, -3], [-1, 3], [2]]
    g = build_graph(clauses, 3)
    assert g.n_vars == 3 and g.n_clauses == 3
    assert g.n_lit_nodes == 6
    assert g.n_edges == sum(len(c) for c in clauses) == 6
    # lit_node mapping
    assert lit_node(1) == 0 and lit_node(-1) == 1
    assert lit_node(3) == 4 and lit_node(-3) == 5
    # flip is an involution pairing complements
    assert g.flip.tolist() == [1, 0, 3, 2, 5, 4]
    assert np.array_equal(g.flip[g.flip], np.arange(6))
    # edges reference the right nodes for the first clause (1, 2, -3)
    c0 = sorted(int(l) for l, c in zip(g.edge_lit, g.edge_clause) if c == 0)
    assert c0 == sorted([lit_node(1), lit_node(2), lit_node(-3)]) == [0, 2, 5]
    # every endpoint in range
    assert g.edge_lit.max() < g.n_lit_nodes and g.edge_clause.max() < g.n_clauses
    print("sat_graph self-test: OK (3 vars, 3 clauses, 6 edges, flip involution)")


def main() -> None:
    if len(sys.argv) == 1:
        _selftest()
        return
    g = from_file(sys.argv[1])
    deg = np.bincount(g.edge_clause, minlength=g.n_clauses) if g.n_clauses else []
    print(f"{sys.argv[1]}")
    print(f"  vars={g.n_vars}  clauses={g.n_clauses}  "
          f"lit_nodes={g.n_lit_nodes}  edges={g.n_edges}")
    if g.n_clauses:
        print(f"  clause arity: min={int(np.min(deg))} "
              f"mean={np.mean(deg):.2f} max={int(np.max(deg))}")
        litdeg = np.bincount(g.edge_lit, minlength=g.n_lit_nodes)
        print(f"  literal degree: mean={np.mean(litdeg):.2f} "
              f"max={int(np.max(litdeg))}")


if __name__ == "__main__":
    main()
