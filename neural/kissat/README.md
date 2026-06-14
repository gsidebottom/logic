# kissat neural phase warm-start (§4b fork)

A minimal, sound patch to **kissat 4.0.4** that seeds `kissat_decide_phase` with
neural-predicted per-variable phases — the §4b substrate for the NeuroBack-style
warm-start (the matrix `eff` engine proved a poor A/B venue; see
[doc/neural_phase1.md](../../doc/neural_phase1.md)).

## What it does

`neural_phase_warmstart.patch` (90 insertions across `decide.c`, `internal.c`,
`internal.h`): when a variable has no target/saved phase yet, kissat uses the
predicted phase in place of the constant `INITIAL_PHASE`. Phases are loaded once
from `$KISSAT_INITIAL_PHASES` (the `neural/phase_infer.py` file format: signed
DIMACS lits, `0`-terminated, `c` comments), mapped internal→external var
**polarity-aware** (`kissat_export_literal`, so kissat's import polarity flips
are undone).

**Sound:** phase saving is a decision-order tiebreaker — clause learning and
DRAT proof emission are untouched. Verified: UNSAT + seed → DRAT →
`gratgen`/`gratchk` still `s VERIFIED UNSAT`. **Polarity correct:** seeding the
*true* model solves `ezfact64_6` in **0 conflicts**; the *inverted* model makes
it worse than baseline.

## Build

```sh
git clone --depth 1 https://github.com/arminbiere/kissat /tmp/kissat-src
cd /tmp/kissat-src
git apply /path/to/neural/kissat/neural_phase_warmstart.patch
./configure && make -j
# patched binary: build/kissat
```

## Use

```sh
# 1. predict phases (CPU-only), high-confidence only
uv run python neural/phase_infer.py --weights neural/weights/phase_v2 \
    --cnf inst.cnf --out inst.phases --margin 0.6
# 2. solve with the warm-start
KISSAT_INITIAL_PHASES=inst.phases /tmp/kissat-src/build/kissat inst.cnf
# A/B harness: neural/ab_kissat.py --kissat <bin> --weights ... --margin ...
```

## Result (honest)

The mechanism is **proven and sound**, but the current predictor (trained on
only **53 structured instances**) does **not** net-beat kissat's strong
built-in phase heuristics on held-out instances:

| margin | conflict ratio warm/base (geomean / median) | wall (base → warm) |
|---|---|---|
| 0.6  | 1.29 / 1.15 | 325 s → 324 s (≈) |
| 0.85 | 1.23 / 1.00 | 332 s → 319 s (−4%) |

High family-dependent variance: big wins on some (`Break_triple` 0.39×,
`toughsat` 0.39×), big losses on others (`med30` 6.9×). The gap is **training
data scale** — NeuroBack trained on *thousands* of instances; the oracle proves
the implementation is correct, so the lever is a much larger labeled corpus
(and/or per-family models), not the fork. All verdicts matched (sound).
