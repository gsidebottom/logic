# neural/ — neural-guided SAT (Phase 0+)

Implementation of the neural-guided SAT plan
([doc/neural_sat_plan.md](../doc/neural_sat_plan.md)). Aristotle-inspired:
MCGS + RL with **machine-verified proofs as the reward**.

**Track A** (near-term, de-risked): a GNN warm-start for the CDCL stage —
reproduce NeuroBack (ICLR 2024: query-once GNN phase prediction → +5–7 % in
kissat, CPU-only), then exceed it. **Track B** (moonshot): LLM proof-step
search over the certified slice.

## Layout

| file | role | status |
|---|---|---|
| `sat_graph.py` | DIMACS → NeuroSAT-style literal–clause bipartite graph (numpy) | Phase 0a |
| `build_dataset.py` | solve curated/GBD instances → per-variable phase labels (from SAT witnesses) → train/test dataset | Phase 0b |
| `model.py` | message-passing GNN (MLX), phase-prediction head; Phase-0 gate | Phase 0c |

numpy-only through Phase 0b; MLX added at the encoder (0c). No GPU needed
for the data foundation; the GNN trains on the M4 Pro via MLX.
