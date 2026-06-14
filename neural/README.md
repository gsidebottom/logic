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
| `backend.py` | runtime ML-backend detection (mlx / torch) | done |
| `build_dataset.py` | solve curated/GBD instances → per-variable phase labels (from SAT witnesses) → train/test dataset | Phase 0b |
| `model.py` | message-passing GNN, phase-prediction head; Phase-0 gate | Phase 0c |

## Setup

`./setup.sh` auto-selects the ML backend by platform — **Apple Silicon →
`mlx`**, **CUDA host (`nvidia-smi`) → `torch`**, else core-only — via the
`mlx` / `torch` optional extras in `pyproject.toml`. Override with
`./setup.sh --ml-backend mlx|torch|none` or `ML_BACKEND=…`. At runtime,
`backend.py`'s `detect_backend()` picks whatever was installed, so model
code stays backend-agnostic.

numpy-only through Phase 0b (no GPU needed for the data foundation); the
GNN (0c) trains on the M4 Pro via MLX, or on the cluster via torch.
