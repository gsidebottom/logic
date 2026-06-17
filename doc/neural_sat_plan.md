# Neural-guided SAT — project plan (MCGS + RL, Aristotle-inspired)

*Approved plan — Phase 0 in progress. Inspired by Harmonic's Aristotle
(arXiv:2510.01346): Monte Carlo Graph Search + a joint policy/value model +
expert iteration, with **machine-verified proofs as the reward**.*

---

## 0. Read this first — the honest framing

There are **two very different SAT analogs of Aristotle**, and conflating
them is the classic way these projects fail:

- **(A) Neural-guided solving** — a learned policy replaces/augments VSIDS
  branching inside CDCL. The "beat kissat" dream.
- **(B) Neural-guided proof search** — MCGS *constructs a refutation*
  (cutting-planes / resolution / cook-style steps), reward = a verified,
  compact proof. This is the *direct* Aristotle analog (Lean tactic search
  → SAT proof-step search).

**The wall that kills naive (A):** kissat makes ~10⁷ branching decisions
per second; VSIDS bumping is O(1). A neural-net forward pass is ~10⁻³ s.
A net call *per decision* is **6–9 orders of magnitude** too slow to be
wall-clock competitive. No neural policy *replaces* a tuned C solver on
general competition instances by wall-clock — and "from-scratch" neural
solvers (NeuroSAT/Graph-Q-SAT) only reduce *decision counts* or win on
*narrow distributions*. **But the amortized warm-start variant measurably
*improves* the SOTA solver:** NeuroBack (ICLR 2024) adds a query-once GNN
phase predictor to **kissat** for **+5.2 % / +7.4 %** on SATCOMP-2022/2023,
**CPU-only at solve time**. That — improving kissat, not beating it
standalone — is the achievable, already-demonstrated target. The ways
around the wall:
1. **Amortize** — call the net rarely (once at root, or per restart), let
   cheap CDCL run millions of decisions between calls. The NeuroCore /
   **NeuroBack** model — empirically validated in kissat.
2. **Distill** — train offline, compile the policy into a cheap hand-coded
   scorer that runs at VSIDS speed; the net never runs at solve time.
3. **Change domains to (B)** — proof *steps* are coarse and expensive
   (apply a lemma, a cardinality reduction), so per-step net cost is
   affordable — exactly why Aristotle works on Lean (dozens of expensive
   steps, not millions of cheap ones).

**Realistic targets (not "beat kissat everywhere"):**
- Near term: **reproduce a NeuroBack-style kissat improvement** (a
  query-once GNN phase/score warm-start, +5–7 %, CPU-only) and beat **our
  own `eff` CDCL** (currently ~26–32 of 400 vs kissat's ~300) — the
  already-demonstrated, achievable win, distilled so it costs nothing at
  solve time.
- Medium term: MCGS proof search that **extends the certified slice** —
  finds compact verified proofs on structured/crafted families where
  today's Cook/parity detectors don't fire.
- Moonshot (honest open problem): general wall-clock parity with kissat via
  GPU-batched amortized inference. Plan toward it; don't promise it.

**Where we are uniquely positioned** (edges generic neural-SAT lacks):
1. **Verification-grounded, reward-hack-proof signal.** cake_lpr/VeriPB are
   our Lean kernel. Reward = *verified* proof; **proof size** is a dense,
   honest quality gradient. A policy can't game a reward it must formally
   prove.
2. **An RL outer loop already exists.** `evo/` (openevolve) already does
   search-policy improvement against a 3-tier, proof-gated evaluator —
   that's expert iteration's scaffold, minus the learned model.
3. **A controllable structured search.** The matrix method's path
   classification is a non-CDCL search surface where MCGS over *paths* is
   genuinely novel (nobody has put MCGS on the connection/matrix method).

---

## 1. Aristotle → SAT mapping

| Aristotle (Lean) | SAT analog |
|---|---|
| MCGS over proof states, transposition = equal goal/context | MCGS over search states, transposition = equal residual formula (CDCL already exploits this via learned clauses) |
| 200B transformer, joint policy+value, on **text** | small **GNN** over the literal–clause incidence graph (state is a graph, not text; and small = trainable on our hardware) |
| Action = Lean tactic string, progressive widening | Action = branch literal (track A) / proof-step lemma (track B); progressive widening over the literal fan-out |
| Reward = Lean kernel verifies (no `sorry`) | Reward = cake_lpr/VeriPB verifies; **+ shorter proof = higher reward** |
| Expert iteration | self-play episodes on training instances → harvest good traces → retrain → repeat |
| Test-time training | per-instance fine-tune on the live search trace (advanced; later) |

**Architecture decision (GNN vs transformer).** For the **Track-A state
encoder, use a GNN, not a sequence transformer** — confirmed by 2024–2026
work: (i) *permutation invariance* (solver behavior must be invariant to
variable/clause relabeling — structural in GNNs, must be *learned* by a
sequence transformer); (ii) *scale* (self-attention is O(n²) over up to
millions of literals; GNN message-passing is O(formula size)); (iii) *data
regime* (graph transformers underperform plain message-passing GNNs when
labeled data is limited and graphs are large — our exact regime: ~800
curated + GBD). The result that actually moved kissat (NeuroBack, +5–7 %)
is a GNN; even the strongest transformer SAT work stays graph-grounded
(SATformer, ICCAD 2023 — a GNN building clause embeddings + a transformer
over them, not raw text). Attention *inside* the GNN (GATv2-style; cf.
SAT-GATv2) is the sanctioned upgrade; a full graph-transformer is a later
experiment only if data scales. **Where a transformer *is* right: Track B**
— the proof-step proposer is text-like, coarse, and few-per-instance, so
attention's cost is affordable and its reasoning/generalization is the
point (Aristotle's transformer on Lean). Our scale-appropriate version: a
**hosted LLM via Bedrock** (already wired into `evo/`) proposes proof steps,
verified by VeriPB/cake_lpr — no model training.

---

## 2. Assets we build on (don't reinvent)

- **`eff` / matrix method** — controllable search; `cdcl.rs` EVOLVE block
  (restart + VSIDS) is the existing tunable policy surface.
- **`evo/` openevolve** — 3-tier evaluator, proof-gated scoring, witness +
  UNSAT-proof gates. This *is* the RL evaluation harness.
- **cover certs + VeriPB + cake_lpr + GN21 parity + Cook provers** — the
  reward oracle and the proof-size signal.
- **hydra** — the portfolio a learned engine slots into (new stage, or
  guidance for the CDCL stage).
- **curated 2025/2026 sets + GBD + `run_benchmark.py`** — training/eval data
  + parallel episode generation, already instrumented for conflicts/
  restarts/proof outcomes.

---

## 3. The plan — phased, each with a hard go/no-go gate

### Phase 0 — substrate: state encoder + offline dataset *(low risk)*
- **Graph encoder.** Implement the literal–clause incidence graph + a
  NeuroSAT-style message-passing GNN (small: ~1–2 M params, ~16–26 rounds,
  per-literal output head). Train/infer with **MLX on the M4 Pro's GPU**
  (unified memory suits GNNs; no cloud GPU needed for this scale) — cloud
  GPU optional later to speed RL.
- **Instrumentation.** Extend `sat`/`eff` to log, per solve: decision
  sequence, conflicts, restarts, final verdict, and (UNSAT) proof size —
  the supervised + RL dataset, harvested via `run_benchmark` over the
  curated sets + GBD, stratified by family with a held-out test split.
- **Gate:** the GNN can predict satisfiability / a decent variable ranking
  on held-out instances above a trivial baseline (sanity that the encoder
  learns SAT structure at all). If not → the encoder/features are wrong;
  fix before spending on search.
- **✓ GATE PASSED (2026-06-13).** `neural/model.py` (MLX NeuroSAT-style GNN,
  64-dim, 16 rounds) on a synthetic random-3-SAT corpus straddling α≈4.26
  (`neural/gen_random.py`; 400 instances, 189 SAT / 211 UNSAT,
  family-stratified 320/80 split): **held-out SAT/UNSAT accuracy 0.812 vs
  0.525 majority** (+0.287, gate ≥ 0.10). Training is stable — loss falls
  0.88→0.39 monotonically; no peak-then-collapse. What was load-bearing:
  SUM (not mean) aggregation to break node symmetry; sqrt(n)-scaled sum
  pooling + LayerNorm; and gradient accumulation over a mini-batch (the
  collapse was batch-size-1 gradient variance). The encoder demonstrably
  learns SAT structure → cleared into Phase 1.

### Phase 1 — reproduce NeuroBack, then distill (track A, the de-risked win)
NeuroBack (ICLR 2024) already demonstrated this exact win — so Phase 1 is
*reproduce-then-own*, not invent.
- **Supervised target = NeuroBack's:** train the GNN to predict each
  variable's **phase** (its value in the majority/all of satisfying
  assignments), the signal NeuroBack showed is what matters — plus an
  optional initial-score head. Labels from the logged solve dataset
  (Phase 0); public NeuroBack code/data to bootstrap and sanity-check.
- **Query-once warm-start.** Run the GNN **once per instance** before
  solving and seed the phase/score arrays — the §4 form factor, **CPU-only
  at solve time** (NeuroBack confirms no GPU needed to deploy). Substrate:
  our `cdcl.rs` EVOLVE block first (we own it + the proof pipeline).
- **Distill** the GNN ranking into a cheap O(1)-feature scorer where even a
  one-shot GNN call is unwanted, so the policy is pure-CPU and fork-free.
- **A/B** through the proof-gated `run_benchmark`, same machine.
- **Gate:** reproduce a **NeuroBack-class improvement** — beat `eff` CDCL,
  and show a measurable kissat gain when the same warm-start is patched into
  kissat (§4b) — while every UNSAT still certifies. This gate is *concrete
  and already-achieved by others*, so failing it means an implementation
  bug, not an open-research wall.
- **◐ PARTIAL (2026-06-14).** Mechanism proven, substrate redirected — see
  [doc/neural_phase1.md](neural_phase1.md). A sparse NeuroSAT per-variable phase
  predictor reaches **0.80 held-out phase accuracy** (vs 0.58 majority) on 53
  structured SAT instances; majority-vote labels (`build_dataset.py --models`)
  beat the single-model MVP. The query-once warm-start hook
  (`sat --initial-phases`, seeding `cdcl.rs` phase-saving) is **sound** and its
  upside is **real**: an oracle (true-model seed) solves in **0 conflicts**, and
  high-confidence seeding (`phase_infer.py --margin`) cut conflicts −59% on the
  one A/B instance that solves. But the matrix `eff` engine proved a **poor A/B
  venue** — nondeterministic and too slow (most medium instances time out), and
  brittle to imperfect priors. The §4b kissat fork was then built
  ([neural/kissat/](../neural/kissat/)): a sound, polarity-verified patch seeding
  `kissat_decide_phase` (oracle → **0 conflicts**). Its A/B on held-out
  instances is **net-negative** (conflict geomean ~1.2–1.3×, wall ≈ neutral) —
  *not* an implementation bug (oracle proves the hook), but an **undertrained
  predictor** (53 instances vs NeuroBack's thousands). **Gate not met; the lever
  is training-data scale** — a large multi-family labeled corpus / per-family
  models. All infrastructure (predictor, inference, cdcl.rs + kissat hooks,
  GRAT-certified A/B) is complete and reusable for that data effort.
- **◑ data-scale lever confirmed (2026-06-14).** Scaled the corpus **53 → 691**
  SAT instances (91 real GBD-pool + 600 generated planted-phase, via
  `neural/gen_structured.py`), retrained `phase_v3`, re-ran the *same* kissat A/B
  on the *same 13 held-out*: total wall **325→324 s (v2) → 328→279 s (v3, −15%)**.
  13× data **flipped the warm-start from neutral to a net wall-time win** (big
  speedups on large SAT instances), all sound — directional confirmation that
  **corpus scale is the lever** (v1→v2→v3: negative → neutral → positive).
  Still high-variance, not yet NeuroBack's clean +5–7%; the full thousands-scale
  corpus (GBD indexes 31k instances) is the path to a robust win.
- **◑ full-scale push (2026-06-14).** Scaled **53 → 2206** (106 real + 2100
  generated plant-labeled-directly-to-npz, no solver, via `neural/gen_npz.py`),
  trained `phase_v4`. Scale **monotonically pushed the A/B conflict geomean
  >1 → <1** (v2 ~1.3 → v3 1.32 → v4 0.95–0.98: net-helping); best wall −5.9%
  (margin 0.85), sound throughout. Wall stays noisy (few big instances flip
  between models). The v4 corpus was synthetic-heavy only because ~106–440 real
  SAT instances were on local disk at the time — **not** a hard limit: real
  instances ARE fetchable via `tools/gbd/download.sh` from benchmark-database.de
  (5,984 SAT ≤50k vars downloadable). A *real* thousands-scale corpus (`phase_v5`)
  is the next step — a download + harvest-compute step. See
  [neural_phase1.md](neural_phase1.md).
- **● real full-scale win (2026-06-15).** Downloaded 2,899 real SAT
  (`tools/gbd/download.sh`), trained `phase_v5` on **2,218 real** instances.
  Best A/B yet: **−28.7% wall** on the 13 held-out, geomean monotonically
  1.32 (v3) → 0.95 (v4) → **0.89 (v5)**, all sound. Real data is decisively the
  lever. Caveats: still high-variance (two big wins dominate; small 13-instance
  test), and the cheap size-band is random-heavy (unpredictable phases →
  internal accuracy gate failed even as the A/B improved). Clean next lever: a
  **structured-only** corpus (3,355 non-random SAT ≤15k downloadable) + a larger
  held-out test for a tight aggregate.
- **○ stabilized (2026-06-15) — the −28.7% was small-sample luck.** Built both
  next levers: a structured-only corpus (`phase_v6`, 1,738 harvested, random
  families dropped) and a **53-instance** held-out. The structured corpus lifted
  the accuracy gate (v5 +0.044 *failed* → v6 +0.050 *passed*), but the larger
  A/B deflated the headline: **geomean 0.953, wall +9.7%** (40 usable, 0
  mismatches) — a modest, broad conflict reduction that is a *net wall loss*
  once a few costly regressions are counted. Honest conclusion: at this
  predictor scale/quality the phase warm-start is **≈ neutral on wall-time**, not
  NeuroBack's +5–7%. The bigger held-out caught the over-claim. See
  [neural_phase1.md](neural_phase1.md) (v6 section).
- **○ bigger/margin levers exhausted (2026-06-15) — bottleneck is the signal.**
  A calibration probe showed v6 is already well-calibrated (ECE 0.049); accuracy
  rises with the margin (0.69→0.95 at M=0.8). But (1) a **4× bigger** model
  (`phase_v7`, dim 128/rounds 24) hit the *same* accuracy ceiling (0.691 vs
  0.689) — capacity is not the lever; and (2) a margin sweep *appeared* to find
  no net win (M=0.7/0.8 byte-identical), **but that was a harness bug**
  (`ab_kissat` infer-path failure → un-seeded warm runs; retracted, fixed in
  `c146799`). The bigger-model finding stands (inference-only probe). **Next
  lever = better labels:** majority-vote phases (`build_dataset.py --models K`).
  See [neural_phase1.md](neural_phase1.md) (v7 section).
- **◑ majority-vote labels WORK on conflicts (2026-06-16).** Re-harvested the
  1,738 structured insts with `--models 16` (median ku=12; 75% differ from
  single-model); trained `phase_v8` on the **soft** target P(True) at v6's exact
  size (so it isolates the labels). Clean A/B (post-bugfix): **v8@0.6 conflict
  geomean 0.851 vs single-model v6's 0.943** — a real lever, with big wins
  (Break_triple 0.36×, WS_500 0.40×, x9 0.41×). **Wall still +10.8%**, but one
  bad apple owns it: a single instance (`19a72fc6`, +106.5s, 12.3×) > the whole
  net loss — excluding it, net **−29s**. That catastrophe has the lowest
  confidence-mass on the set → next lever is **per-instance gating / runtime
  abstention**. See [neural_phase1.md](neural_phase1.md) (v8 section).
- **● WALL WIN (2026-06-17) — labels + confidence-mass gate.** Added
  `phase_infer --gate FRAC`: skip seeding any instance whose fraction of
  margin-clearing vars is `< FRAC` (diffuse predictions → catastrophic-regression
  risk; the `19a72fc6` disaster has only 6.7% coverage). Clean A/B, v8 @ M=0.6:
  **gate=0.10 → wall −4.0%** (geomean 0.891), **gate=0.15 → wall −6.1%**
  (geomean 0.876), 0 mismatches — vs ungated +10.8%. **First real, sound net
  wall win** in the phase-warm-start line. Needs *both* levers: majority-vote
  soft labels (signal) + the gate (abstain on diffuse predictions); bigger models
  and margin tuning did nothing. Caveat: gate threshold tuned in-sample (both
  values win, so not a knife-edge); one high-confidence-but-wrong regressor
  (`3c15c8fb`) is uncatchable by a confidence gate. See
  [neural_phase1.md](neural_phase1.md) (v8 + gate section).
- **○ two refinements tried, both negative (2026-06-17).** *Backbone-only*
  seeding (v8 @ high margin 0.85/0.9) is **neutral** (±0.1%) — too few seeds,
  discards the wins with the losses. A *learned* gate (logistic / Δwall-ridge,
  leave-one-out, simulated via `gate_loo.py` from the measured A/B — no new
  runs) **can't beat the blunt threshold**: catastrophes are not predictable
  from prediction features (`19a72fc6` +106s vs `1c3abce4` +5s have ~identical
  features → it's solver-dynamics, not GNN-output). **Final config stands:** v8
  @ M=0.6 + confidence-mass gate (−4 to −6%).
- **◑ solver-dynamics probe-gate: a race reaches the oracle, but costs a core
  (2026-06-17).** Since catastrophes are visible to the *solver* not the GNN,
  **race** seeded vs unseeded and take the first to finish. Simulated exactly
  from measured `base_s`/`warm_s` (`probe_gate.py`) + validated with real
  concurrent runs (contention ~3%): **probe race T_p=30s → −15.1% wall at 1.49×
  CPU**; full portfolio −15.5% at 1.69×. That's **3× the threshold gate's win**,
  recovering the oracle the feature-gate couldn't. *But* a cheap early-commit via
  intermediate dynamics fails — conflicts@5s predict the winner only 48% (coin
  flip), so you must actually run the race (a 2nd core) for the −15%. Net: single
  core → confidence-mass threshold (−4 to −6%); spare core → parallel race
  (−15%, never regresses). See [neural_phase1.md](neural_phase1.md)
  (probe-gate section).

### Phase 2 — RL / expert iteration (track A, exceed the teacher)
- **Reward** = solved (binary) + shaping: −log(decisions) for speed, and
  for UNSAT **−proof_size** on the *verified* proof (reward-hack-proof).
- **Loop** (expert iteration): run amortized-inference MCGS/policy episodes
  on training instances → keep traces that beat the current best →
  retrain → repeat. Reuse `evo/`'s evaluator as the scoring/gating stage.
- **Inference = amortized only** (root + per-restart variable-priority
  refocus, NeuroCore-style), or fully distilled per iteration — never
  per-decision.
- **Gate:** on a **chosen target distribution** (start where eff is least
  embarrassing — small structured/crafted families), the learned policy
  beats both `eff` and the kissat-in-hydra baseline at equal wall-clock.
  Hard kill if RL doesn't exceed Phase-1 imitation after N iterations
  (precedent: our search-side ideas — rephasing, inprocessing — all
  measured negative; this gate respects that).

### Phase 3 — MCGS proof search for the certified slice (track B, the Aristotle analog)
- **The true analog.** MCGS *constructs* a refutation: actions are
  proof-steps (cutting-planes ops, cardinality/at-most-1 reductions,
  cook-style lemmas, XOR eliminations) over the PB/clausal state; a node is
  a derived-constraint set; terminal = empty clause / 0≥1.
- **Reward** = a **verified, compact** proof (VeriPB/cake_lpr) — proof size
  is the optimization target, exactly like Aristotle minimizing Lean proof
  effort. Per-step net cost is affordable here (coarse expensive steps).
- **Target:** structured/crafted UNSAT families *beyond* what the current
  hand-written detectors (PHP/RR/clique/mchess/parity) cover — i.e. *learn*
  to find Cook-style proofs the detectors miss. Also the matrix-method
  path-MCGS variant (novel; high risk).
- **Gate:** finds verified proofs on ≥1 family no current detector handles,
  competitive in size/time. This is the highest-novelty, highest-ceiling,
  most-"us" track — and the most uncertain.

### Phase 4 — moonshot: general wall-clock parity *(open research)*
- GPU-batched amortized inference (batch many nodes/instances per forward
  pass to hide latency, the trick that made GNN branching work for MILP,
  Gasse et al. 2019), test-time training, larger models.
- Framed explicitly as an **open problem**, gated on Phases 1–3 actually
  producing wins. Not a deliverable promise.

---

## 4. Integration form factor — where the learned policy actually runs

Make-or-break engineering: a policy is only useful if it plugs into a fast
solver *without* paying per-decision net cost (the §0 wall). Three
substrates, in order of effort:

**(a) Our `cdcl.rs` EVOLVE block — recommended starting substrate.** We
already carved restart + VSIDS as a policy seam; a distilled scorer or a
learned initial-phase/score vector drops straight in. We own it — no fork,
no upstream churn, full control of the proof pipeline. Cost: our CDCL is
slower than kissat's hand-tuned C, so a win here proves the *policy* helps
but doesn't by itself give kissat-speed-plus-policy.

**(b) kissat — fork + patch, not API.** kissat's public API (`kissat.h`) is
deliberately minimal — add/solve/value, scalar options, limits, terminate;
**no assumptions, no phase-setting, no priority injection** (the
non-incremental design, and exactly why NeuroCore/Graph-Q-SAT used
MiniSat/Glucose, which expose an overridable `pickBranchLit` / `setPolarity`
/ assumptions). Injection means forking and patching internals — but the
seams are small and localized (~675 LOC across the relevant files):
- *Learned initial phases* (warm start): `kissat_decide_phase` (`decide.c`)
  falls back to a constant `INITIAL_PHASE`; seed a predicted phase array
  instead — one function, the cheapest hook.
- *Distilled scorer*: seed/replace the `scores` heap in `decide.c`.
- *NeuroCore-style periodic refocus*: `rephase.c` is already a switch over
  phase-reset strategies — add a neural variant, or re-seed scores in
  `kissat_restart`.

A branching/phase patch changes *which* decisions, not the clause-learning
or proof machinery, so **DRAT/LRAT emission and cake_lpr certification
survive unchanged.** The real cost is maintenance: re-applying patches
across a fast-moving upstream and respecting kissat's data layout so the
patch doesn't wreck its speed.

**(c) MiniSat / Glucose — least resistance for a faithful reproduction.**
Clean C++ extension points; if we just want to *reproduce* NeuroCore /
Graph-Q-SAT before innovating, this is the fastest substrate — at the cost
of a much weaker base solver than kissat.

**The realistic "neural + fast solver" form factor:** a GNN-predicted
**initial phase vector and/or initial score vector**, computed **once per
instance** and seeded into the solver's arrays at init — one net call, the
solver runs untouched afterward, patching only the init path (NeuroSAT
warm-start pattern). NeuroCore's periodic refocus is the next rung up.
Per-decision net guidance stays off the table.

**Sequencing:** prove the policy in (a) `cdcl.rs` first (cheap, no fork tax,
our proof pipeline) → only if it clearly wins, fork-patch (b) kissat for its
raw speed under the learned policy. Keep kissat *untouched* as the hydra
baseline/competitor until then.

---

## 5. Compute & infrastructure

- **Model scale:** small GNN (~1–2 M params), *not* a 200B transformer —
  trainable + inferable with **MLX on the M4 Pro** for the amortized/
  distilled tracks. Cloud GPU is optional to accelerate Phase-2 RL, not
  required to start.
- **Data generation:** CPU-bound solve episodes, already parallelized by
  `run_benchmark` (`-j10`) over curated sets + GBD.
- **The RL loop** reuses `evo/`'s evaluator + proof gates; the new piece is
  the learned model replacing LLM-evolved code in the improvement step.
- **Languages:** GNN/training in Python (MLX/PyTorch); the distilled scorer
  and any amortized-inference hook in Rust (`cdcl.rs`), called over a thin
  FFI/IPC boundary or compiled to a feature-weight table for zero-overhead.

---

## 6. Risks & kill criteria

| risk | mitigation / kill |
|---|---|
| **Inference cost wall** (dominant) | amortize or distill from day one; Phase-1 gate is explicitly speed-competitiveness, not accuracy |
| RL never exceeds imitation | hard kill after N iterations (our search-side track record says be ruthless) |
| Reward hacking | impossible by construction — reward requires a *verified* proof |
| No GPU / compute | MLX on M4 Pro covers Phases 0–1; cloud only if Phase 2 warrants |
| "Beat kissat" overclaim | the framing forbids it as a near-term target; wins are vs `eff`/on-distribution, with kissat as north star |
| Distribution overfit | held-out test split + per-family stratification from Phase 0 |

---

## 7. Recommendation

Start **Phase 0 → 1** (encoder + dataset + imitation + distilled policy
for `eff`): low cost, reuses `evo/` + `run_benchmark`, runs on the M4 Pro,
and produces a *useful artifact even if the moonshot stalls* — a stronger
`eff`/hydra CDCL. **Gate hard** before Phase 2 RL.

If forced to pick one track for upside-with-identity, it's **Phase 3
(track B)**: neural proof search with verified-proof-size reward is the
genuine Aristotle analog, plays to our unique assets (the only project here
nobody else is positioned to do), and sidesteps the inference-cost wall
that blocks the "beat kissat" framing. Track A is the safe, incremental,
hardware-friendly warm-up; track B is the actual moonshot.

**Decision needed from you:** (a) approve Phases 0–1 as the start; (b) which
target distribution for the Phase-1/2 gate; (c) appetite for cloud GPU if
Phase 2 clears its gate; (d) relative priority of track A (stronger eff)
vs track B (learned proof search) for the ambitious phase.

---

## 8. References

**Foundational neural SAT (2018–2020)** — define the wall: from-scratch
neural solving reduces *decision counts* / wins on *narrow distributions*,
never beating a tuned C solver standalone by wall-clock:

- **NeuroSAT** — D. Selsam, M. Lamm, B. Bünz, P. Liang, L. de Moura,
  D. L. Dill. *Learning a SAT Solver from Single-Bit Supervision.*
  ICLR 2019. [arXiv:1802.03685](https://arxiv.org/abs/1802.03685). A
  message-passing GNN over the literal–clause graph that learns to predict
  satisfiability (and decode assignments) — the proof-of-concept that GNNs
  capture SAT structure; our Phase-0 encoder follows it.
- **NeuroCore** — D. Selsam, N. Bjørner. *Guiding High-Performance SAT
  Solvers with Unsat-Core Predictions.* SAT 2019 (Theory and Applications
  of Satisfiability Testing), Springer.
  [arXiv:1903.04671](https://arxiv.org/abs/1903.04671). The system
  introduced is named *NeuroCore*: a GNN periodically refocuses a real
  CDCL solver's (MiniSat/Glucose) variable activity toward predicted
  unsat-core variables — the canonical *amortized* integration (net called
  rarely, not per decision) that Phase 2 mirrors.
- **Graph-Q-SAT** — V. Kurin, S. Godil, S. Whiteson, B. Catanzaro. *Can
  Q-Learning with Graph Networks Learn a Generalizable Branching Heuristic
  for a SAT Solver?* NeurIPS 2020.
  [arXiv:1909.11830](https://arxiv.org/abs/1909.11830). Value-based RL (DQN)
  with a GNN learns a MiniSat branching heuristic; cuts *iterations* and
  generalizes across sizes, but is not wall-clock competitive — the direct
  precedent (and cautionary tale) for Track A.

**Recent neural SAT (2023–2026)** — the action moved to *amortized
warm-start* (which works) and *attention-augmented / hybrid* models:

- **NeuroBack** — W. Wang, Y. Hu, M. Tiwari, S. Khurshid, K. McMillan,
  R. Miikkulainen. *NeuroBack: Improving CDCL SAT Solving using Graph Neural
  Networks.* ICLR 2024. [arXiv:2110.14053](https://arxiv.org/abs/2110.14053).
  **The Phase-1 template:** a GNN predicts variable phases, queried **once**
  before solving and seeded into **kissat** → **+5.2 % / +7.4 %** on
  SATCOMP-2022/2023, **CPU-only at solve time**. Public code. The concrete,
  already-achieved version of our near-term target.
- **SATformer** — Shi et al. *SATformer: Transformer-Based UNSAT Core
  Learning.* ICCAD 2023.
  [arXiv:2209.00953](https://arxiv.org/abs/2209.00953). A **hybrid** — a GNN
  builds clause embeddings, a hierarchical transformer models their
  correlation (cuts CaDiCaL/kissat solve time on LEC). Evidence the best
  "transformer for SAT" stays graph-grounded, not raw-text.
- **SAT-GATv2** — Chang & Liu. *A Dynamic Attention-Based GNN for Solving
  the Boolean Satisfiability Problem.* Electronics (MDPI) 2025. Attention
  *inside* the GNN (GATv2) — the sanctioned upgrade over plain MPNN.
- **Boolean Satisfiability via Imitation Learning** —
  [arXiv:2509.25411](https://arxiv.org/abs/2509.25411) (2025). Supports
  Phase 1's imitation step.
- **Neural Approaches to SAT Solving: Design Choices and Interpretability**
  — [arXiv:2504.01173](https://arxiv.org/abs/2504.01173) (2025). Survey of
  the design space.
- **G4SATBench** — [arXiv:2309.16941](https://arxiv.org/abs/2309.16941)
  (2023). GNN-for-SAT benchmark; scaffolding for Phase-0/1 evaluation.

Adjacent precedent and inspiration:

- **GNN branching for MILP** — M. Gasse, D. Chételat, N. Ferroni,
  L. Charlin, A. Lodi. *Exact Combinatorial Optimization with Graph
  Convolutional Neural Networks.* NeurIPS 2019.
  [arXiv:1906.01629](https://arxiv.org/abs/1906.01629). Learned
  branch-and-bound variable selection that *does* beat hand-crafted rules —
  because MILP nodes are expensive (an LP solve each) and inference is
  GPU-batched. The existence proof for the amortization argument in Phase 4.
- **Aristotle** — T. Achim et al. (Harmonic). *Aristotle: IMO-level
  Automated Theorem Proving.* 2025.
  [arXiv:2510.01346](https://arxiv.org/abs/2510.01346). MCGS + joint
  policy/value model + expert iteration with **Lean-kernel-verified reward**
  and test-time training — the blueprint this plan adapts (Track B is its
  SAT-proof-search analog, with cake_lpr/VeriPB as the kernel).
