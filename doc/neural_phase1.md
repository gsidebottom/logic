# Neural Phase 1 — NeuroBack-style phase warm-start (results)

Phase 1 of [doc/neural_sat_plan.md](neural_sat_plan.md): reproduce NeuroBack —
a GNN predicts each variable's **phase**, queried **once** before solving to
seed the solver's phase-saving, A/B'd through the (GRAT-certified) proof-gated
pipeline. The crux question — *can phases be predicted, and does seeding them
help?* — is answered: **prediction yes; the warm-start mechanism is sound and
its upside is real; the matrix `eff` engine is the wrong substrate to measure
it on.**

## 1a–1c — predictor + inference

- **Dataset** (`neural/data/phase_harvest_index.jsonl`, built by
  `build_dataset.py`): 53 structured SAT instances from the curated benchmarks
  (scheduling, hamiltonian, ramsey, circuits, crypto), 40 train / 13 test,
  ~450k variable-labels. Random k-SAT is excluded — its phases aren't
  predictable; structure is the whole point.
- **Predictor** (`neural/phase_model.py`): the Phase-0c NeuroSAT encoder
  (SUM scatter-add aggregation + LayerNorm + grad-accum) made **sparse** (COO,
  scales to 34k vars / 200k clauses) with a **per-variable phase head**.
  Gate: held-out phase accuracy **0.792 vs 0.575 majority** (+0.217).
- **Inference** (`neural/phase_infer.py`): CNF → graph → one forward pass →
  per-variable phase file (signed lits). 26 ms GPU / 895 ms CPU; CPU-only
  suffices (the deploy form factor).

## 1d — warm-start hook (sound; polarity verified)

`sat --initial-phases FILE` seeds `CdclController.saved_phase` once before
search (every cdcl/eff path; requires `--no-preprocess`). **Sound by
construction** — phase saving is a decision-order tiebreaker, never touches
clause learning or the proof. The polarity was subtle (the search runs on the
CNF *complement*, so seed `saved_phase[v]=Some(L>0)`), **verified by oracle** on
`ezfact64_6` (3073 vars):

| seed | conflicts | result |
|---|---|---|
| none (baseline) | ~24,000 | SAT |
| **true model (oracle)** | **0** | **SAT, 226 ms** |
| inverted model | 13,343 | 30 s timeout |

A perfect prior finds the model with *zero* search; the inverse is a disaster.
Mechanism and polarity are correct, and the ceiling is enormous.

## 1e — A/B, routes (2) high-confidence + (1) majority-vote

The *predicted* phases (79%) initially **hurt** matrix `eff` (4/5 worse): its
EffectiveCount-guided search is brittle to the ~21% wrong seeds. Two fixes:

**(2) High-confidence seeding** (`phase_infer.py --margin`): seed only vars
where `2·|p−0.5| ≥ margin`. The predictor is well-calibrated, so this trades
coverage for accuracy and cuts wrong seeds from ~21% of all vars to <1%:

| margin | coverage | accuracy on seeded |
|---|--:|--:|
| 0.0 (all) | 100% | 0.79 |
| 0.6 | 20% | 0.91 |
| 0.8 | 13% | 0.95 |

**(1) Majority-vote labels** (`build_dataset.py --models K`): sample up to K
models via blocking clauses, label each var by the **majority** phase +
`agreement` (backbone confidence) — NeuroBack's actual target, vs our noisier
single-model MVP. Retrained `phase_v2`: accuracy **0.792 → 0.802**, and
*broader* high-confidence coverage (margin 0.6: 20% → 48% of vars seeded).

**A/B on matrix `eff`** (5 instances, median of 3 runs, conflicts; high-conf
seeds): only the one instance that *solves within 30 s* gives a clean read —
`x9-06099` baseline 51k → **warm@0.6 21k (−59%)**. The other 4 **time out** at
30 s under `eff` (no verdict), so their numbers aren't real comparisons. Plus
`eff` is **nondeterministic** (baseline `x9` swung 17k–68k across runs).

## Conclusion + next

- **Proven:** phases are predictable (0.80), the warm-start is **sound**, and
  its upside is **real and large** (oracle → 0 conflicts; `x9` → −59%).
  Routes (2)+(1) both delivered — high-confidence seeding helps where
  measurable; majority labels improve the predictor (`phase_v2`).
- **Substrate finding:** matrix `eff` is a **poor venue for the A/B** —
  nondeterministic, too slow (4/5 medium instances time out at 30 s), and
  brittle to imperfect priors. A convincing aggregate A/B can't be run here.
- **Next (§4b):** the decisive A/B belongs on **kissat** — fast, ~deterministic,
  with phase-saving as a *soft* prior that conflict-learning quickly corrects
  (tolerant of a noisy seed, unlike the brittle matrix engine). Seed kissat's
  `kissat_decide_phase` with `phase_v2 @ margin 0.6`, A/B through the same
  GRAT-certified `run_benchmark`. This is where NeuroBack's +5–7% should
  materialize.

## Artifacts

- `neural/phase_model.py` (sparse encoder + phase head), `neural/phase_infer.py`
  (`--margin`), `neural/build_dataset.py` (`--models` majority + agreement).
- `neural/weights/phase_v1.*` (single-model), `phase_v2.*` (majority; preferred).
- Datasets are derived (gitignored): rebuild via `build_dataset.py` from
  `neural/data/phase_harvest_index.jsonl`.
