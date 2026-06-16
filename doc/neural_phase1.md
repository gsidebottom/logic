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

## §4b — kissat fork (executed)

The recommended next step, now done ([neural/kissat/](../neural/kissat/)). A
90-line patch to kissat 4.0.4 seeds `kissat_decide_phase` from
`$KISSAT_INITIAL_PHASES` (in place of the constant `INITIAL_PHASE`; target/saved
phase-saving still win), internal→external var mapping polarity-aware.

- **Sound + correct:** UNSAT + seed → DRAT still `gratchk`-certifies; oracle
  (true model) → **0 conflicts**, inverted → worse than baseline (polarity
  verified). kissat is deterministic, so the A/B is clean.
- **A/B (13 held-out instances, `phase_v2`):** **net-negative** — conflict
  ratio warm/base geomean **1.29** @ margin 0.6 (wall ≈ neutral), **1.23**
  @ margin 0.85 (median 1.00, wall −4%). High family variance: big wins
  (`Break_triple`, `toughsat` ~0.4×) cancelled by big losses (`med30` 6.9×).
- **Diagnosis:** *not* an implementation bug (the oracle proves the hook is
  perfect) — the **predictor is undertrained** (53 instances vs NeuroBack's
  thousands), so its held-out phases aren't reliable enough to beat kissat's own
  heuristics. The gate (NeuroBack-class win) is **not met**; the lever is
  **training-data scale** (a large multi-family labeled corpus and/or per-family
  models), which is a data effort, not a mechanism one. Infrastructure (fork,
  inference, A/B, GRAT certification) is complete and reusable for that.

## §4b data-scale follow-up — the lever confirmed

The §4b diagnosis (undertrained predictor) predicted that *more data* should
help. Tested it: scaled the corpus **53 → 691** SAT instances — 91 real (broad
GBD-pool harvest, `neural/data/v3_real_index.jsonl`) + 600 generated
structured-with-planted-phases (`neural/gen_structured.py`: planted graph
k-coloring + planted k-SAT). Retrained **`phase_v3`**, re-ran the *same* kissat
A/B on the *same 13 held-out* real instances:

| predictor | corpus | A/B total wall (base → warm, margin 0.6) |
|---|--:|---|
| phase_v2 | 53 | 325 → 324 s (≈ neutral) |
| **phase_v3** | **691** | **328 → 279 s (−15%)** |

13× more data **flipped the warm-start from neutral to a net wall-time win**:
big speedups on the large SAT instances (`Break_triple` 70→21 s, `WS_500`
63→21 s) outweigh small regressions. All verdicts sound. Honest caveats: it's
**high-variance** (a few big wins + a few regressions, not uniform), the
conflict-ratio geomean still reads >1 (dominated by *tiny* instances where
absolute cost is negligible), and it's **margin-sensitive** (0.6 wins; 0.85
seeds too few vars → neutral). So this is a **directional confirmation**, not yet
NeuroBack's clean +5–7% — the trend across v1→v2→v3 (negative → neutral →
positive) shows the lever is corpus scale, and the full thousands-scale corpus
(GBD has 31k indexed instances) is the path to a robust win.

### Full-scale push (phase_v4, 2206 instances)

Pushed the corpus **53 → 2206** SAT instances: **106 real** (all on-disk SAT
≤50k vars per GBD's `result` feature, minus the 13 held-out) + **2100 generated**
(`neural/gen_npz.py` — planted coloring/k-SAT/PHP-SAT written *directly to npz*
with plant-phase labels, **no solver**, ~5 s for 2100). Retrained `phase_v4`,
re-ran the same kissat A/B:

| predictor | corpus | best wall (13 held-out) | conflict geomean |
|---|--:|---|--:|
| phase_v2 | 53 | ≈ neutral | ~1.3 |
| phase_v3 | 691 | −15% (margin 0.6, noisy) | 1.32 |
| **phase_v4** | **2206** | **−5.9% (margin 0.85)** | **0.95–0.98** |

Scale **monotonically pushed the conflict geomean from >1 (hurting) to <1
(net-helping)** — the `med30` 6.9× regression at v2 became a 0.23× *win* at v4 —
a genuine, scale-driven improvement; wall-time stays net-positive (−2 to −6%)
but **noisy** (the 13-instance set is dominated by a few big instances that flip
win↔loss between models). Sound throughout (all verdicts matched).

**Why this corpus was synthetic-heavy (and the fix):** at v4 only ~106–440
*real* SAT instances were on local disk, so I padded with synthetic — whose
transfer to the real test families is limited + noisy. (An earlier note here
wrongly said the rest of GBD's 31k index "can't be fetched" — **it can**:
`tools/gbd/download.sh "result=sat and variables<N"` pulls CNFs from
benchmark-database.de by GBD query; **5,984 SAT ≤50k vars are downloadable**.)
The mechanism + scaling law are proven; a *clean, robust* NeuroBack +5–7% needs
**thousands of real instances**, which is a download + harvest-compute step —
now underway (`phase_v5`).

### Real full-scale (phase_v5) — the data-scale win

With the fetch path open (`download.sh`), pulled **2,899 real SAT instances**
(4,016 on disk, 11 GB) and built a **3,014-real-SAT** index (≤15k vars, minus
the 13 held-out), harvested **2,218** (single-model), trained **`phase_v5`
(real-only)**. Same kissat A/B, same 13 held-out:

| predictor | corpus | wall (13 held-out) | conflict geomean |
|---|--:|---|--:|
| phase_v3 | 691 (91 real) | −15% | 1.32 |
| phase_v4 | 2206 (106 real) | −5.9% | 0.95 |
| **phase_v5** | **2218 real** | **−28.7%** | **0.891** |

**Best result across the whole sweep** — geomean monotonically 1.32 → 0.95 →
0.89, wall −28.7% (311→222 s), all 13 verdicts sound. Real data is decisively
the lever (e.g. `WS_500` 2.6M→162K conflicts, `Break_triple` 1.8M→379K).

Two honest caveats:
- **Still high-variance:** the −28.7% is dominated by two huge wins
  (`WS_500` 0.06×, `Break_triple` 0.21×) against real regressions (`x9`, `mp1`
  ~1.7×); the geomean 0.89 is the steadier read. The 13-instance held-out set is
  too small for a tight aggregate — a larger test set is needed for a
  publication-grade number. **→ The v6 round below built that 53-instance
  held-out, and it deflated this −28.7% to +9.7% wall: the win was small-sample
  luck.**
- **Accuracy ≠ utility, and corpus *quality* matters:** v5's internal accuracy
  gate *failed* (margin +0.044) because the cheap small-size band is
  **random-heavy** (uniform-random/random/hidden-model ≈ 1,200 of 3,014), whose
  phases are unpredictable — yet the *structured* real instances (hamiltonian,
  planning, coloring, factoring…) carried the downstream A/B win. So random
  families are dead weight; the clean next lever is a **structured-only** corpus
  (**3,355 non-random SAT ≤15k vars are downloadable** — hamiltonian 775, crypto
  383, planning 241, coloring 189, …), which should lift accuracy *and* the A/B.

### v6 — structured-only corpus + larger held-out (the honest correction)

Two fixes to pressure-test the v5 win: **(1)** a **structured-only** training
corpus (2,248 → 1,738 harvested; dropped the random families) and **(2)** a
**larger held-out** (53 structured instances vs the noisy 13), with a
time-capped, unfinished-excluding A/B harness.

- **(1) worked on accuracy:** the gate flipped from v5's failing **+0.044 →
  +0.050 PASSED** — removing random families (unpredictable phases) cleaned the
  signal (modestly).
- **(2) overturned the headline.** On 40 usable held-out instances:

  | metric | v5 (noisy 13) | **v6 (53 held-out)** |
  |---|---|---|
  | conflict geomean | 0.891 | **0.953** |
  | total wall | **−28.7%** | **+9.7%** |

  The warm-start gives a *modest, broad* conflict reduction (geomean 0.95,
  ~13 wins / 17 ties / 8 losses) but is a **net wall-time loss (+9.7%)**: a few
  instances regress badly (the predicted phase sends kissat down a worse path)
  and cost more wall-time than the many small wins save. **v5's −28.7% was
  small-sample luck** — two huge wins on 13 instances. All 53 sound (0
  mismatches).

**Honest bottom line.** At this predictor scale/quality, the neural phase
warm-start is **≈ neutral-to-slightly-negative on wall-time** (modestly positive
on conflicts) — *not* NeuroBack's clean +5–7%. The mechanism is sound (oracle →
0 conflicts) and phases are weakly predictable (~0.69–0.80), but the per-instance
variance — costly regressions on a minority — sinks the wall aggregate once the
test set is big enough to be trustworthy. NeuroBack's win likely needs its
combination we don't have here: a much larger model + majority-vote labels + a
PAR-2-style metric over a large benchmark (which rewards many small speedups and
is less hurt by a few regressions). **The larger held-out earning this
correction is the main result of this round** — it caught an over-claim the
13-instance set had hidden.

### v7 — "bigger / better-calibrated" predictor + margin sweep (negative result)

Tested the two obvious levers on the v6 result. First a **calibration probe**
(`neural/calibrate.py`) on the v6 labeled test split (351 insts): v6 is already
**well-calibrated** (ECE 0.049), and accuracy *climbs* with the confidence
margin — 0.689 (all) → 0.885 (M=0.6) → **0.948 (M=0.8)**. So the +9.7% A/B
(seeded at M=0.6, where ~11.5% of seeds are wrong) looked like a *threshold*
problem, not a model-quality one. Two follow-ups:

1. **Bigger model (`phase_v7`: dim 64→128, rounds 16→24, ~4× params, +0.05
   label smoothing).** Hit the **same accuracy ceiling** (micro 0.691 vs v6's
   0.689) and, because smoothing curbs confidence, ended up with **less than
   half** v6's high-confidence-correct mass at every margin (M=0.8: 2.4% vs
   5.4% coverage). Capacity is **not** the bottleneck — the ceiling is how
   learnable these phases are from structure.

2. **Margin sweep on v6 — ⚠ CORRUPTED by a harness bug, retracted.** The
   original sweep reported M=0.7/0.8 as **byte-identical ties** (geomean 1.000),
   which I misread as "seeds vanish → signal is the bottleneck." That was **not
   real**: `ab_kissat`'s `--infer` default failed silently when the driver was
   run from `neural/` (it looked for `neural/neural/phase_infer.py`), reusing a
   *stale* phase file, so the warm runs were **un-seeded** → false ties (fixed in
   `c146799`; see the v8 section). The bigger-model result (1) stands — it rests
   on the inference-only calibration probe, which the bug never touched.

**Conclusion (corrected).** *Capacity* is not the lever (v7 hit v6's accuracy
ceiling). The real margin/label behavior — measured on the **fixed** harness —
is in the v8 section below, and it shows the **labels** are a genuine lever.

### v8 — majority-vote soft labels (the labels ARE the lever) + a harness bug

Took the "better labels, not a bigger net" shot. Re-harvested the **same 1,738
structured instances** with `build_dataset.py --models 16` (vote over up to 16
blocking-clause models; median ku=12; **75%** of instances got labels that differ
from single-model), and trained `phase_v8` at **v6's exact architecture** (dim
64, rounds 16) on the **soft target** P(True)=agreement (`--soft-labels`) — so
any change is the labels, not capacity. The soft target teaches the net to
abstain (≈0.5) on free vars and be confident only on backbones.

- **Gate:** micro 0.721 vs majority 0.667 (+0.054); already > v6's 0.689.
- **Calibration probe (vs v6):** seeds are markedly cleaner — at M=0.6
  **94.3%** accurate (v6: 88.5%), and **~70% more** high-confidence-correct mass
  at M=0.8 (9.2% coverage @ 96.7% vs v6's 5.4% @ 94.8%).

**⚠ Harness bug found mid-run.** Early v8 A/Bs came back byte-identical — the
same `ab_kissat` infer-path failure above. A hand check exposed it: v8 actually
drives `x9` from 609569 → **252118** conflicts (**−57% wall**) while the harness
reported a tie. Fixed (`c146799`: cwd-independent infer path, fail-loud on infer
error, fresh phase file per instance, phase/CNF var-count check). **All
this-session A/Bs before the fix were no-seed artifacts.**

**Clean A/B (fixed harness), 53-instance held-out:**

| run | conflict geomean | wall | wins/ties/losses |
|---|--:|--:|--:|
| **v8@0.6** (soft majority) | **0.851** | +10.8% | 11/21/7 |
| v8@0.7 | 0.969 | +15.5% | 7/28/5 |
| v6@0.6 (single-model, same harness) | 0.943 | +8.8% | 13/19/7 |

**The labels worked on what they target:** v8@0.6 conflict geomean **0.851** vs
single-model v6's 0.943 — a real, substantial improvement, with big wins
(`Break_triple` 0.36×/−47.5s, `WS_500` 0.40×/−38.6s, `Break_14` 0.12×/−13.1s,
`x9` 0.41×/−7.6s). **But wall is still net-positive (+10.8%)** — and it's *one
bad apple*: net Δ = +190.7s regressions − 113.2s savings = **+77.5s**, of which a
**single** instance (`19a72fc6`) is **+106.5s** (12.3×). Excluding just that one,
v8@0.6 is a net wall **win (−29s)**; excluding the top two, −90s.

**Remaining obstacle = tail-risk, not signal.** The catastrophe `19a72fc6` has
the **lowest** confidence-mass of any instance (meanConf 0.192, only 6.7% of vars
> 0.6) — a diffuse, low-information prediction. A "skip seeding when
confidence-mass is low" **gate** would drop it (→ net win), though it's imperfect
(`3c15c8fb` +60.8s is high-confidence yet regressed). So the corrected bottom
line: majority-vote labels are a genuine lever (conflicts ↓, seeds cleaner); the
path to a wall win is **per-instance gating / runtime abstention** on the few
catastrophic regressions, not a bigger model or a different margin.

## Artifacts

- `neural/phase_model.py` (sparse encoder + phase head; `--label-smooth`,
  `--soft-labels`), `neural/phase_infer.py` (`--margin`),
  `neural/build_dataset.py` (`--models K` majority-vote + agreement),
  `neural/calibrate.py` (reliability/ECE + accuracy-at-margin probe),
  `neural/ab_kissat.py` (kissat A/B; cwd-independent infer, fail-loud).
- `neural/weights/phase_v6.*` (single-model, structured), `phase_v8.*`
  (soft majority-vote, **best conflicts**; trained at v6's dim 64/rounds 16).
- Datasets are derived (gitignored): rebuild via `build_dataset.py` from
  `neural/data/phase_harvest_index.jsonl`.
