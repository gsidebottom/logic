#!/usr/bin/env python3
"""
Phase 1c — query-once phase inference: CNF -> predicted per-variable phases.

Loads the trained phase predictor (phase_model.py --save) and runs it ONCE on
an instance's literal-clause graph to produce a preferred initial phase for
every variable. Emits a phase file the solver reads to warm-start phase-saving
(`sat --initial-phases FILE`, the §4a cdcl.rs hook).

This is the deploy form factor: one net call per instance, before solving;
the solver runs untouched afterward. CPU-only is sufficient (NeuroBack), but on
Apple Silicon MLX uses the GPU by default — pass --cpu to force CPU.

Phase file format (DIMACS-ish, easy to parse in Rust): the predicted preferred
polarity of each variable as a signed literal (+v = phase True, -v = False),
whitespace-separated, terminated by `0`. Comment lines start with `c`.

Usage:  phase_infer.py --weights neural/weights/phase_v1 [--cnf FILE|-]
                       [--out FILE|-] [--cpu]
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time

import numpy as np
import mlx.core as mx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sat_graph                                   # noqa: E402
from phase_model import PhaseNet                   # noqa: E402


def graph_to_inst(g: "sat_graph.SatGraph") -> dict:
    n_vars = g.n_vars
    return {
        "el": mx.array(g.edge_lit), "ec": mx.array(g.edge_clause),
        "flip": mx.array(g.flip),
        "n_lit": g.n_lit_nodes, "n_cls": g.n_clauses, "n_vars": n_vars,
        "pos": mx.arange(n_vars) * 2, "neg": mx.arange(n_vars) * 2 + 1,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--weights", required=True,
                    help="base path (loads PATH.safetensors + PATH.json)")
    ap.add_argument("--cnf", default="-", help="DIMACS CNF (default: stdin)")
    ap.add_argument("--out", default="-", help="phase file (default: stdout)")
    ap.add_argument("--cpu", action="store_true", help="force CPU inference")
    ap.add_argument("--margin", type=float, default=0.0,
                    help="emit only high-confidence phases: seed variable v iff "
                         "2*|p-0.5| >= margin (0=all; 0.8 ≈ top-confidence ~13%% "
                         "at ~95%% accuracy).  Unseeded vars use the solver default.")
    args = ap.parse_args()

    if args.cpu:
        mx.set_default_device(mx.cpu)

    base = args.weights[:-len(".safetensors")] if args.weights.endswith(".safetensors") \
        else args.weights
    cfg = json.load(open(base + ".json"))
    model = PhaseNet(cfg["dim"], cfg["rounds"])
    model.load_weights(base + ".safetensors")
    mx.eval(model.parameters())

    t0 = time.time()
    if args.cnf == "-":
        # parse_dimacs wants a path; spill stdin to a temp file
        import tempfile
        with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as tf:
            tf.write(sys.stdin.read()); cnf_path = tf.name
        g = sat_graph.from_file(cnf_path); os.unlink(cnf_path)
    else:
        g = sat_graph.from_file(args.cnf)

    prob = np.array(mx.sigmoid(model(graph_to_inst(g))))   # (n_vars,) P(phase=True)
    phases = prob >= 0.5
    conf = 2.0 * np.abs(prob - 0.5)                         # 0..1 confidence
    keep = conf >= args.margin                              # high-confidence only
    dt = time.time() - t0

    lits = [((v + 1) if phases[v] else -(v + 1))
            for v in range(g.n_vars) if keep[v]]
    out = sys.stdout if args.out == "-" else open(args.out, "w")
    out.write(f"c phase predictions: {g.n_vars} vars, {g.n_clauses} clauses, "
              f"seeded {len(lits)} (margin {args.margin}), "
              f"{int(phases[keep].sum())} True ({dt*1000:.0f} ms)\n")
    for i in range(0, len(lits), 20):
        out.write(" ".join(map(str, lits[i:i + 20])) + "\n")
    out.write("0\n")
    if out is not sys.stdout:
        out.close()
        print(f"c wrote {g.n_vars} phases → {args.out} ({dt*1000:.0f} ms)",
              file=sys.stderr)


if __name__ == "__main__":
    main()
