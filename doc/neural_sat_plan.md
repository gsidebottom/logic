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

- **○ ExIt headroom de-risk KILLS one-shot-seeding ExIt (2026-06-17).** Iteration
  1's rollout step (`neural/exit_rollout.py`): sample K phase-seedings from v8,
  run kissat, keep the best by conflicts. Headroom looked huge — best-of-5 /
  argmax geomean **0.465** (−54% conflicts beyond v8). **But the control killed
  it:** *uniform-random* seeds do equally well (best-of-5 / argmax **0.449**;
  v8-best beats uniform-best on only 23/59). So the gain is **seed-variance, not
  learnable signal** — kissat's heavy-tailed runtime (Gomes et al.) means
  best-of-K exploits randomization luck, which a one-shot policy can't distill.
  v8's argmax is still good (it beats the *mean* sample, 1.65×), but ExIt can't
  improve it. The same heavy-tail obstacle applies to VSIDS-*score* seeding
  (CDCL runtime is chaotic regardless of phase vs score), so that's not pursued
  either. **The real best-of-K win (−66% conflicts) is a *portfolio*** (random
  restarts / multi-seed), captured by parallelism — the same lesson as the
  probe-race. The only ExIt variant with a non-chaotic, learnable objective is
  Phase 3 (proof construction; proof-size is deterministic).

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

- **● Phase-3 env BUILT + de-risk GREEN (2026-06-17).** `neural/cp_search.py`: a
  cutting-planes proof-search environment — PB constraints, `pol` actions (add /
  multiply / divide-with-ceiling = Chvátal–Gomory cut), terminal `0>=1`, emits a
  VeriPB `.pbp` and **independently verifies** every proof found. Best-first
  (unguided) search results:
  - self-tests (trivial `{x}{¬x}`; an LP-infeasible CNF needing multiply): both
    construct + **veripb-VERIFIED** proofs.
  - **PHP-3-2** (pairwise CNF — LP-feasible, resolution-*hard*): unguided search
    finds a **verified** CG proof in **12 nodes** *with* the divide rule;
    FM-only (no divide) correctly fails — isolating CG-rounding as essential.
  - **PHP-4-3** (one size up): **explodes** — 30k nodes, no proof, with or
    without divide. This is the learnable frontier.
  So the construct-and-verify loop is real, search finds small proofs of a
  resolution-hard family, and the bottleneck is precisely *search guidance at
  scale*. Unlike the killed seeding-ExIt, the objective is **deterministic + the
  derivations are structured (learnable)**, not chaotic runtime luck. Next: a
  learned policy to score `pol` derivations (bootstrap from found proofs + the
  Cook generators), then ExIt to scale to PHP-4-3+/non-PHP families.
- **● Phase-3 step-1 (hand-guidance de-risk): guidance IS the lever
  (2026-06-18).** Replaced the generic `(nvars,-rhs)` heuristic with **slack**
  (`Σ positive-coeffs − rhs` — drive the LP relaxation toward infeasibility). FM
  + divide, no same-sign: PHP-3-2 in 8 nodes; **PHP-4-3 in 389 nodes / an
  80-derivation verified proof — vs the baseline heuristic FAILING at 30k
  nodes** (~100× node reduction from the heuristic alone). The same-sign
  "cardinality-building" action *explodes* branching (PHP-3-2: 12 nodes →
  minutes) — a red herring; FM+divide+slack is the right config. So the search
  is **strongly guidable** (30k-fail → 389) — the precondition for a learned
  policy (better policy → fewer nodes → bigger proofs). Caveat: the per-node
  engine cost is high (PHP-4-3: 389 nodes but 477s — pool × divisor branching),
  an optimization orthogonal to the guidance question.
- **◐ Phase-3 step-2a BLOCKED — the engine, not learnability, is the wall
  (2026-06-19).** Built the feature-scorer imitation infra (`cp_policy.py`:
  record which expanded constraints land on the proof path → logistic priority)
  but couldn't get a clean result: the prototype `cp_search.py` is
  **catastrophically inefficient** — the *legitimate* PHP-4-3 search generates
  **>5,000,000 constraints (gigabytes)** to find an 80-step proof (it prunes
  nothing, adding every FM+divide combination), at ~1.2s/node. So recording one
  proof takes ~8 min + GBs; PHP-5-4 is out of reach; the proof sits at the
  search's exhaustion edge (389 nodes). (Also surfaced + fixed a 9-hour runaway:
  a diverged logistic → NaN priority → unbounded pool → 11.7 GB; hardened with a
  stable fit, NaN-guarded learned priority, and a `max_secs` wall-time guard —
  the real runaway bound. A guessed `max_pool` cap is *not* safe: it kept cutting
  off legitimate searches, which need a >5M pool on this engine. See
  [[bound-and-watch-background-compute]].)  **Verdict:** the concept is validated
  (step-1) but the Python engine is a slow, memory-explosive sketch unfit for the
  iterative learned-policy loop. **Critical path before resuming 2a/2b: an engine
  rewrite** — aggressive subsumption/dominance pruning (pool should be thousands,
  not millions), efficient structures, likely Rust alongside the Cook/PB infra —
  so proofs are found with headroom and recording is tractable.
- **○ Engine rewrite attempt 1 — pruning is the wrong fix; need a new algorithm
  (2026-06-19).** Added sound **canonicalization** (`PB.canonical()`:
  literal-normalize → saturate → exact-gcd divide, behind `cp_search --prune`) to
  collapse the scalar-multiple / over-strong-coeff duplicate families. Measured on
  PHP-4-3: pool **5M → 2.8M (only ~2×)**, 383 nodes, 357s — *insufficient*. The
  pool is **genuinely-distinct constraints**, and blind best-first FM-against-the-
  whole-pool **generates ~2.8M constraints to find a 74-step proof** (~38,000×
  overhead); the *generation* (O(pool) candidates/node × hundreds of nodes), not
  storage, is the cost — so subsumption pruning won't fix it either (it still has
  to generate+test millions). **The right architecture is the LP-guided
  cutting-plane method** (how ILP/PB solvers refute): solve the LP relaxation, add
  one *violated CG cut*, repeat until infeasible → Farkas combination = the proof
  — ~one constraint per cut (dozens), goal-directed. Bonus: **"which cut to add"
  is exactly the learned-policy hook** (Gasse et al. GNN cut-selection for MILP),
  so it unifies the efficiency fix with the Phase-3 learning goal. Cost: needs an
  LP solver (scipy — *not installed*; add dep or hand-roll Farkas) + CG-cut and
  Farkas→`pol` emission. A substantial fresh build, not an incremental patch.
- **● LP-CG engine, Phase A DONE — goal-directed Farkas refutation
  (2026-06-20).** Added scipy; `neural/cp_lp.py`: the **signed-variable Farkas
  LP** (maximize Σ y·rhs s.t. Σ y·coef[i]=0 ∀i, y≥0, normalized) → rationalize
  the ray → integer multipliers → emit one `pol Σ mⱼ·Cⱼ` = 0≥positive →
  **veripb VERIFIED**. Validated on three LP(ℝ)-infeasible cases (lp_infeasible
  (1,1,2); amo3; chain) — each a *single* LP solve + *single* pol line, instant,
  no pool. This is the architecture working: goal-directed, O(1) constraints vs
  the blind engine's millions. **Next (Phase B):** the CG-cut loop for
  LP-feasible-but-UNSAT systems (PHP class) — add variable bounds, and when the
  LP is feasible separate a violated Chvátal-Gomory cut, add it, repeat until
  infeasible → Farkas. CG *separation* is the crux (Gomory-from-basis or a
  separation search) and is exactly where the learned cut-selection policy lives.
- **● LP-CG Phase B — PHP-3-2 CRACKED end-to-end, verified (2026-06-20).** The
  cutting-plane loop (`cp_lp.py --cg`): LP over [0,1] → if infeasible, Farkas;
  else separate violated **{0,1/2}-cuts** (mod-2 / GF(2): a 0/1 constraint combo
  with all-even coeffs + odd degree, CG-rounded — these *are* the PHP cardinality
  cuts) → add, repeat. Emission chains each cut (`pol <Σsel> 2 d`) then the final
  Farkas. Result: **PHP-3-2 refuted in 6 cuts → veripb VERIFIED**, goal-directed
  and instant — vs the blind engine's ~5M constraints / 477s. The architecture is
  validated end-to-end on a resolution-hard instance.
  - **Limitation (resolved below):** {0,1/2}-cuts stall on PHP-4-3/5-4 — even
    pigeon-count holes put each var in an *odd* number of pairwise AMOs, so the
    full cardinality isn't a single mod-2 cut (PHP-5-4 gets `Σ≤2`, not `≤1`).
    These need **general CG cuts** (divisors >2).
- **● LP-CG Phase C — general CG cuts; PHP-4-3 CRACKED + verified (2026-06-20).**
  Added Fischetti–Lodi-style CG separation, but with **integer multipliers per a
  fixed divisor q** (`_modq_separate`, swept q=2..qmax): an all-integer MILP picks
  `w_j ∈ {0..q-1}` maximizing the violation of `divide(Σ w_j·C_j, q)`. Integer w
  (not rationalized floats) makes the cut **exact and emittable** as
  `pol Σ w_j·C_j q d` — the {0,1/2} case is just q=2. (A first attempt rationalized
  scipy's float multipliers; messy denominators → huge LCM → `divide` degenerated,
  so the reconstructed cut wasn't the one the MILP found. Integer-per-q fixes it.)
  - **Anti-stall is the other half.** Single-vertex (max-Σx), single-best-cut
    separation hits the first CG closure while the LP is still feasible and stalls
    (PHP-4-3 at 4–5 cuts). Fix in `cg_loop`: **rotate LP objectives** (expose
    different vertices) and **add *all* distinct violated cuts** each round. With
    that: **PHP-3-2 → 8 cuts, PHP-4-3 → 12 cuts, both refuted in round 0 → veripb
    VERIFIED.** PHP-4-3 is the instance {0,1/2}-cuts alone could not crack.
  - **PHP-5-4: the loop *progresses* but naive separation doesn't *scale*.** It
    climbs (20→48 cuts) but never finishes cheaply — re-separating the whole
    growing system across ~12 objectives × ~10 divisors per round explodes in time
    (round 7 ≈ 360 s; per-MILP `time_limit=5 s` added as a guard). This is exactly
    the motivation for the **learned cut-selection policy**: replace the
    brute-force "separate everything, add everything" with a policy that picks the
    *few* cuts that drive toward infeasibility (GNN over the LP+constraint state →
    which cut, à la Gasse et al.). That is the next step, now well-motivated by a
    concrete scaling wall rather than a guess.
- **● LP-CG cut-selection policy — learned scorer → VERIFIED proof, 2.3× fewer
  cuts (2026-06-20).** `cp_cut_policy.py`. **Imitation**: run the brute-force loop,
  trace the final Farkas support *backward through the cut derivations* to label
  each added cut useful/not, fit a logistic scorer over 9 cheap cut features, then
  re-run keeping only the top-scored fraction per round.
  - The premise holds: only **25–38 %** of brute-force cuts are useful (the rest
    are wasted). Learned weights are interpretable — keep cuts that combine *fewer*
    constraints (`nsrc −1.2`), have a smaller max coefficient (`maxc −1.0`), and
    higher violation/degree.
  - **Result: on PHP-4-3 the policy refutes in 12 cuts vs 28 for add-all in the
    same loop (2.3×), and the policy-selected proof emits → veripb VERIFIED** (7 of
    12 cuts in the Farkas support). A learned policy producing a machine-checked
    proof — the Aristotle loop realized on cutting-planes.
  - **Limitation:** PHP-5-4 not yet cracked by the policy. The scorer filters cuts
    *after* separation, so it shrinks system growth but not per-round MILP cost;
    and convergence at that size needs a stronger loop. Scaling further wants the
    policy to choose which *(objective, divisor)* to **separate** (cut MILP count,
    not just additions) and/or a **GNN over the constraint graph** (richer than 9
    hand-features) — the clear Phase-4 direction.
- **● LP-CG separation-CHOICE policy + PHP-5-4 wall diagnosed (2026-06-20).**
  `cp_cut_policy.sep_choice_loop`. Diagnosis first: useful cuts concentrate in the
  **cheap q=2 GF(2)** separator while the per-q MILPs (q≥3) are **~88 % wasted**
  (PHP-4-3: q=2 → 9 useful, q=3..10 MILPs → 2). So tiered/lazy separation — run
  q=2 every round, fire the expensive MILPs **only in rounds where q=2 is
  exhausted**.
  - **Bounds the cost (its design goal): PHP-3-2 → 6 cuts / 0 MILP calls,
    PHP-4-3 → 11 cuts / 1 escalation round / 1.2 s, both veripb VERIFIED.** No more
    wandering MILP explosion.
  - **PHP-5-4 wall re-diagnosed: it's separator *completeness*, not cost.** The
    policy bounds PHP-5-4 to ~100 s (no explosion) but it still **stalls at ~31–36
    cuts**. The decisive check: at the stall, the **exact any-multiplier CG
    separation MILP still finds violated cuts (viol 0.5–0.75)** that the
    uniform-denominator mod-q — even sweeping q≤20 — **misses** (those cuts need
    non-uniform multipliers / an LCM-denominator >20). So PHP-5-4 is *not* at the
    integer hull and *not* cost-bound — the mod-q separator is **incomplete**.
  - **Next lever: a complete separator (decision = GMI from an exact tableau).**
    The cheap alternatives are now *ruled out by measurement*, not guessed:
    - **mod-q at higher Q is dead.** At the PHP-5-4 stall the exact any-multiplier
      F-L MILP still finds violated cuts (viol 0.5–0.99), but **mod-q finds nothing
      at Q∈{6,12,24,30,48,60,LCM}** — these cuts are *not* expressible as `w/Q`.
    - **Float-multiplier recovery is dead.** The F-L MILP's `u` come back as
      numerical noise (per-constraint denominators in the thousands, LCM ≈ 10⁴⁵) —
      a degenerate/non-unique multiplier vector, un-rationalizable. The cut
      `(α,zb)` is exact (integer MILP vars) but its *emittable* multipliers are not
      recoverable from the float `u`.
    - So the complete separator must produce cuts with **exact rational multipliers
      by construction** → **Gomory cuts from the simplex tableau**: the optimal
      basis-inverse row `B⁻¹ᵢ` gives exact multipliers (common denominator
      `det(B)`), the Gomory fractional cut `Σ frac(āⱼ)xⱼ ≥ frac(βᵢ)` cuts the LP
      optimum by construction, and it emits as `pol Σ (det(B)·B⁻¹ᵢ)·Cⱼ  det(B) d`.
    - **Build (next session — self-contained, no dep):** `highspy` is absent and
      `scipy.linprog` doesn't expose the basis, and PHP LP optima are **degenerate**
      (float basis reconstruction is fragile) → build a small **exact rational
      simplex** (Fractions, Bland's rule) on the standard form (`−coef·x ≤ −rhs`,
      `x ≤ 1`, slacks). From its optimal tableau: pick a fractional basic var →
      Gomory cut → eliminate slacks back to a CG cut over the PB constraints +
      `x≤1` bound axioms → emit pol + final Farkas → veripb. Iterate (Gomory's
      finite convergence) to refute PHP-5-4/6-5. **Then** layer MCGS + a
      policy/value GNN + expert iteration on this matured env (the re-aligned
      Aristotle track).
- **● Complete separator BUILT — GMI from an exact tableau cracks the PHP-5-4
  wall, veripb VERIFIED (2026-06-21).** `neural/cp_gmi.py`, self-contained (no
  LP dep). A small **exact rational simplex** (Fractions, two-phase, Bland's rule
  for the degenerate PHP optima) on the standard form (`Σa·x − s_j = b_j`,
  `x_v + t_v = 1`, all vars ≥0); from a fractional basic row the Gomory cut
  `Σ frac(āⱼ)yⱼ ≥ frac(βᵢ)` reads off as **nonnegative rational multipliers by
  construction** — by column meaning: the `s_j` column → multiplier on `Cⱼ`, the
  `x_v` column → on the `x_v ≥ 0` axiom, the `t_v` column → on the `x_v ≤ 1`
  axiom. Scaling by the common denominator D gives integers; the cut emits as one
  CG step `pol Σ λ·Con D d` (constraint ids + the veripb literal axioms `xv` /
  `~xv`, both confirmed pushable). The simplex is cross-checked against scipy
  (38 random LPs: optimum + infeasibility); the cuts are checked violated at x*
  before adding.
  - **Results (cutting-plane loop, rotated objectives, add-all violated Gomory
    cuts → exact-LP infeasible → Farkas, every proof veripb-VERIFIED):
    PHP-3-2 → 1 cut, PHP-4-3 → 17 cuts / 0.5 s, PHP-5-4 → 38 cuts / 3.9 s,
    PHP-6-5 → 102 cuts / 41 s.** The PHP-3-2 cut is literally the cardinality cut
    `x1+x3+x5 ≤ 1`; the proofs at 5-4+ use the bound axioms (general Gomory, not
    just q=2 mod-2).
  - **This is the wall.** The mod-q separator *stalled* PHP-5-4 at ~31–36 cuts
    and never reached infeasibility (incomplete — those cuts need non-uniform
    multipliers). The exact-tableau Gomory separator is **complete**: it refutes
    PHP-5-4 deterministically and scales past it (6-5). The exact LP also removes
    the degeneracy/float-basis fragility that motivated the hand-rolled simplex.
  - **Next:** the env is matured — layer MCGS + a policy/value GNN + expert
    iteration (the re-aligned Aristotle track). "Which fractional row / which cut
    to keep" is the learned-policy hook, now on a complete, fast, exact separator.
- **● Generality sweep — ONE Gomory engine subsumes the five per-family Rust
  detectors at small scale (2026-06-21).** `neural/cp_sweep.py`. Context: PHP is
  *already* handled efficiently by `cook_pbp.rs` (PHP-8-7 → poly proof, veripb
  VERIFIED, 1.1 ms), so cracking PHP with Gomory is engine *validation*, not a
  result that beats a detector. The real question: is exact-tableau Gomory a
  *general* engine or a PHP toy? Sweep over small UNSAT instances, comparing the
  structural detectors (`cook_pbp` shape-match, `xor_gauss` XOR-recovery) against
  the single GMI engine (all veripb-VERIFIED):
  - **parity (Tseitin cycles C3..C9):** cook=no-match, xor_gauss=solves; **GMI =
    1 cut** (one {0,1/2} CG cut does the GF(2) contradiction).
  - **graph-coloring (odd cycles C5..C9, 2-col):** cook=no-match, **xor_gauss
    can't finish (mixed → falls through to the general matrix search)** — i.e.
    *both* structural detectors miss it; **GMI = 1 cut**, VERIFIED. A concrete
    "beyond the structural detectors" datapoint.
  - **mutilated chessboard (4×4, 4×6):** cook detects; GMI = 5 cuts / 1.8 s and
    35 cuts / 93 s, VERIFIED.
  - **PHP-4-3 (baseline):** cook detects; GMI = 17 cuts.
  So one algorithm with no per-family pattern-matching produces machine-checked
  proofs across PHP / parity / coloring / mutilated-chessboard, including a family
  (coloring) the hand-detectors miss. **Limit quantified:** the pure-Python
  `Fraction` simplex is comfortable to ~20–30 vars, slow by ~34 (4×6 = 93 s) — so
  the engine's value is as the *small-instance learning environment*, not a scale
  competitor to the Rust detectors. The gap-family direction (a resolution-hard
  family no detector handles) and the learning track are both now well-founded.
- **◐ Gap-family probe — subset-cardinality is outside all detectors + GMI-verified,
  but "hard + no-detector" is gated by SCALE (2026-06-21).** Target: a family that
  is resolution-hard AND no detector matches AND GMI cracks (the Phase-3 gate,
  concretely). Chose **subset-cardinality** (`cp_sweep.subset_cardinality_cnf`):
  on a 3-regular bipartite graph each left vertex needs ≥2-of-3 edges TRUE, each
  right vertex ≤1-of-3 → Σ ≥ 2n yet ≤ n → UNSAT. Only binary clauses ⇒ LP-feasible
  (`farkas_refute` on the raw clauses = None) ⇒ genuinely needs CG cuts.
  - **Outside all detector coverage** (cook_pbp: no-match; xor_gauss: miss — not
    PHP/XOR/clique/mchess), and **GMI refutes it veripb-VERIFIED**, hand-checked
    (the cut `divide(C1+C2+C3,2)` = the row cardinality `x1+x2+x3≥2`; Farkas over
    it + binary clauses → 0≥1), scaling to n=30 / **90 vars** / 1 cut / 12.6 s.
  - **But it is NOT hard at reachable scale.** GMI cracks it in **1 cut** for every
    n; the general Rust solver in **2 conflicts / 0.5 ms**. Resolution-hardness of
    subset-cardinality / Tseitin / etc. is *asymptotic* (needs large expanders) —
    there is no "small + resolution-hard": at any fixed small size everything is
    absolutely easy. PHP-5-4 ("38 cuts at 20 vars") is the closest small-but-cut-
    heavy instance, and it is *detected*.
  - **The binding constraint is SCALE, and precisely so.** The prototype handles
    *(many vars, few cuts)* — subset-card 90 vars/1 cut/12.6 s — OR *(few vars,
    many cuts)* — mutilated 4×6 34 vars/35 cuts/93 s — but NOT the genuinely-hard
    regime *(many vars × many cuts)*: each cut re-solves the growing system with
    `Fraction` arithmetic, so cost ≈ cuts × tableau-resolves compounds. So a
    compelling hard-gap result **requires the engine to scale first** (faster
    exact LP: bounded-variable form to drop the x≤1 rows, warm-start/incremental
    re-solve, or a Rust port). Until then GMI's demonstrated niche is generality
    (one algorithm, verified, across families incl. ones no detector matches), not
    hardness.
- **● Rust port of the GMI engine — ~15× via i128 rationals, soundness preserved
  (2026-06-21).** `src/gmi.rs` + `src/bin/gmi` (DIMACS stdin → VeriPB `.pbp`),
  alongside the `cook_pbp` / `parity_pbp` detectors. The numeric core is generic
  over a `Scalar` field; it runs a **fast `i128`-rational path first and falls
  back to `BigRational`** on failure.  Key soundness argument: the scalar is only
  a *search* device — the i128 simplex finds the cuts and the Farkas combination,
  but the emitted proof is reconstructed in exact `BigInt`, its Farkas step is
  checked to cancel to `0≥1` exactly, and VeriPB verifies independently.  So an
  i128 overflow (arithmetic wraps, never panics) can only trigger a fallback,
  never an unsound proof; an iteration cap backstops loop termination.
  - **First a `BigRational`-only port was merely ~1.6× over Python** (php-6-5
    41 s→26 s) — bignum heap-alloc per op dominates, like Python's `Fraction`. The
    `i128` path gives the real unlock: **php-5-4 0.19 s, php-6-5 1.77 s (15× over
    BigRational, ~23× over Python), php-7-6 370 cuts / 35 s** — 7-6 was out of
    reach for the Python prototype.  All veripb-VERIFIED; the parity/coloring/
    subset-card families stay 1 cut.
  - **Next:** push the ceiling (php-8-7+) and revisit the hard-gap / learning
    tracks now that medium instances are tractable; warm-start re-solve is the
    next orthogonal speedup (avoid from-scratch two-phase after each cut).
- **● Warm-start re-solve — dual simplex after each cut; ceiling php-7-6 → php-9-8
  (2026-06-21).** `src/gmi.rs` `Warm`/`gmi_loop_warm`. The cold loop re-solves the
  whole growing system from scratch every round × objective — the *(many vars ×
  many cuts)* wall.  Warm-start keeps ONE persistent tableau: after adding a cut
  (one row + one surplus column, expressed in the current basis so the new slack
  is basic-negative) the old optimum is dual-feasible but primal-infeasible in
  just that row → a few **dual-simplex** pivots (Bland, capped) restore optimality
  instead of a full two-phase; an objective rotation keeps primal feasibility → a
  **primal** re-opt, no phase 1.  `refute()` now runs warm-i128 first, cold
  `BigRational` as the trusted fallback.  Soundness unchanged (warm only *finds*
  the cuts/Farkas; proof is BigInt-exact + veripb-checked).
  - **Speedup over cold-i128, growing with size (all veripb-VERIFIED):
    php-5-4 0.19→0.029 s, php-6-5 1.79→0.13 s (13.7×), php-7-6 35→1.7 s (20×).**
    Warm even finds *fewer* cuts (7-6: 256 vs 370) — re-optimizing to a true
    vertex each step beats cold add-all-then-rebuild.
  - **Ceiling moved two levels: php-8-7 (56 vars) 9.6 s / 682 cuts and php-9-8
    (72 vars) 87.6 s / 1810 cuts, both veripb-VERIFIED** — cold-i128 couldn't do
    php-8-7 in 200 s.  vs the original Python prototype (php-6-5 41 s → 0.13 s)
    that is **~315×**.
  - **Next:** the engine now reaches medium instances — revisit the hard-gap and
    learning tracks (cut-selection is the learned hook and *also* shrinks the cut
    count); maintain an incremental objective/cost row to drop the per-pivot
    reduced-cost recompute for a further constant factor.
- **● Learned cut-selection on GMI — imitation scorer, ~2× fewer cuts, transfers,
  veripb-VERIFIED (2026-06-21).** `neural/cp_gmi_policy.py`. The warm engine made
  the *cut count* the bottleneck; this is the Aristotle analog on the complete
  separator (cf. the earlier `cp_cut_policy` on the *incomplete* mod-q one).
  - **Headroom confirmed:** trace the final Farkas support backward through each
    cut's `lamC` (source constraints) → only **~30 % of add-all GMI cuts are
    useful** (php-4-3 32 %, 5-4 30 %, 6-5 31 %); ~70 % are wasted.
  - **Imitation:** fit a logistic scorer over 9 cheap cut features (label =
    useful), then keep the top fraction per round.  Interpretable weights — prefer
    **higher violation** (+0.87), **fewer source constraints** (nsrc −1.8,
    nbound −1.8), **smaller max coefficient** (−1.3): sparser/simpler cuts are the
    useful ones (same lesson as the mod-q policy).
  - **Result (top-50 %/round, all veripb-VERIFIED): php-5-4 56→24 cuts (2.3×),
    php-6-5 111→59 cuts (1.9×) — and 6-5 is OUT-OF-SAMPLE** (trained on
    3-2/4-3/5-4).  A learned policy producing machine-checked proofs, transferring
    small→large; also faster (fewer cuts → smaller growing system).
  - **Next:** port the scorer into the Rust warm loop to apply selection at scale
    (cut the ~1810 cuts on php-9-8, push toward 10-9); then a GNN over the
    constraint graph / expert iteration (richer than 9 hand-features) is the
    Phase-4 direction, now on a fast complete separator.
- **● Learned policy ported to the Rust warm engine — cut reduction GROWS with
  scale, up to 5.3× (2026-06-21).** `src/gmi.rs` `cut_score` + `refute_policy`
  (bin `--policy [--topfrac f]`).  The 9-feature imitation scorer trained in
  Python (effective weights w/sd hard-coded; only the ranking matters) is applied
  in `gmi_loop_warm`: each round keep the top `topfrac` of violated cuts by score.
  No retraining — the *same* scorer (trained on php-3-2/4-3/5-4) transfers to the
  fast warm engine.  Soundness unchanged (selection only drops candidate cuts;
  proof BigInt-exact + veripb-checked; cold add-all fallback).
  - **A/B add-all vs policy (top-50 %/round), all veripb-VERIFIED:
    php-7-6 256→110 cuts / 1.7→0.7 s (2.3×), php-8-7 682→171 / 9.6→4.4 s (4.0×),
    php-9-8 1810→341 / 87.6→16.5 s (5.3×).** The reduction *grows* with instance
    size — the learned policy is increasingly valuable exactly where add-all
    explodes.  This is the learned cut-selection win realized at scale on a fast,
    sound, machine-checked engine — the Phase-3 / Aristotle loop, end to end.
  - **The policy also pushes the CEILING, not just the cut count: php-10-9 (90
    vars) — which add-all could NOT refute in 300 s — is cracked in 574 cuts /
    167 s, veripb-VERIFIED** (the smallest of the `benchmarks/php` instances).
    Learned selection turns a previously-out-of-reach instance into a solved,
    machine-checked one.
  - **Next:** a GNN over the constraint graph + expert iteration for the per-step
    *(row, divisor)* choice (richer than 9 hand-features), now on a fast, sound,
    complete separator.
- **◐ GNN cut-scorer de-risk — representation is NOT the lever on PHP; search is
  (2026-06-21).** `neural/cp_gmi_gnn.py`.  Before a GNN-inference-in-Rust port +
  expert iteration, the gate question: does a GNN over the constraint graph
  predict cut-usefulness *better* than the 9 hand-features?  Built it (MLX,
  bipartite var×constraint message-passing à la Gasse et al.: var nodes
  [x*, fractionality], constraint nodes [rhs, slack@x*, is-candidate], edges =
  coefficients, per-candidate readout), imitation-trained on the same Farkas-
  support labels, A/B on held-out php-6-5 cut-usefulness accuracy:
  - **majority 0.637 · logistic (hand-features) 0.961 · GNN 0.912.** The GNN
    clearly *learns* structure (0.91 ≫ 0.64) but **does not beat the intrinsic
    features**, despite seeing strictly more (x*, slacks, full graph).
  - **Why:** PHP is highly symmetric — every cut is structurally alike, so the
    discriminative signal is *intrinsic* (how violated / how sparse / coefficient
    size), not *relational*.  The cheap features already capture it (~0.96).  The
    less-symmetric families where a GNN might win (subset-cardinality, mixed) are
    CG-trivial (1 cut, no selection to learn).
  - **Verdict:** representation is not the bottleneck for GMI cut-selection on the
    families we can test — so **no Rust-GNN port**.  The genuine high-ceiling lever
    is **expert iteration / search** (find shorter cut sequences than add-all+
    imitation can, retrain on them — proof size is the deterministic reward), and/
    or harder non-symmetric instance families.  Negative result that prunes the
    cheap-but-wrong path, exactly like the mod-q→GMI decision.
- **● Harder testbed FLIPS the verdict — GNN beats hand-features on asymmetric
  graph-PHP → representation IS a lever (2026-06-21).** `cp_sweep.graph_php_cnf`:
  sparse RANDOM bipartite pigeonhole (P pigeons, P−1 holes, random hole-subset per
  pigeon).  UNSAT by matching infeasibility regardless of the graph; keeps PHP's
  cut-heavy cardinality structure but **breaks the symmetry** (every hole's
  incident set differs); cook_pbp = no-match.  Validated cut-heavy via the Rust
  engine (g8-7: 29–167 cuts by density, all veripb-VERIFIED).  Re-ran the GNN-vs-
  logistic A/B (held out across random instances) — and the result **reverses**:
  - **symmetric PHP-6-5:  logistic 0.96 > GNN 0.91** (intrinsic features suffice)
  - **asymmetric graph-PHP-6-5:  GNN 0.92 > logistic 0.88** — and the logistic
    *drops* (0.96→0.88) because intrinsic features can't tell *which* hole-set a
    cut touches, while the GNN sees it.
  The direction-flip is exactly the symmetry hypothesis confirmed: **representation
  helps precisely when structure varies.**  So the GNN frontier is real on
  realistic (low-symmetry) families — and a Rust-native GNN (**Burn**, running
  inside the warm loop, no Python↔Rust boundary) is the justified next build, with
  data generated by the fast Rust engine (cold Python times out at g8-7).
  - **Caveat:** measured as cut-usefulness *prediction* accuracy on small (6-5)
    instances; next is end-to-end (Burn GNN in the loop) + larger g-PHP, then
    expert iteration on top.
- **◐ Burn build started — framework de-risk GREEN (2026-06-21).** Toward a
  Rust-native GNN in the warm loop (the graph-PHP flip justified it).  Added
  `burn = "0.21"` as an **optional** dep behind a `gnn` feature + isolated bin
  `gmi_train` (`required-features=["gnn"]`), so the default `sat`/`gmi` builds
  never pull burn.  Gate: does Burn compile + train a custom multi-layer module
  here?  **Yes — an MLP fits a linear target, loss 1.399 → 0.0007 (2110×).**
  Three Burn-0.21 gotchas cost the most time (now documented in `gmi_train.rs`):
  the `#[derive(Module)]` backend generic **must be named `B`** (the derive
  hardcodes that ident → otherwise broken codegen); **do not** add a manual
  `#[derive(Clone)]` (the Module derive emits an *id-preserving* Clone; a
  field-wise one reassigns `Param` ids and silently freezes training); and use the
  `relu` *function*, not a stored non-generic `Relu` module field.
- **● Burn GNN trains in Rust + reproduces the g-PHP flip (2026-06-21).** The bulk
  landed: (1) `gmi::gen_data` instruments the warm engine to dump per-round
  `Snapshot`s (constraint system + x* + candidate cuts) labeled by the transitive
  Farkas support — fast (i128), all-Rust (cold Python timed out at g8-7); the
  recorder is guarded so the hot refute path pays nothing.  (2) `gmi_train` (bin,
  `--features gnn`) reimplements the bipartite var×constraint message-passing GNN
  in Burn + a graph-PHP generator + a logistic baseline, all in Rust.
  - **A/B (held-out g-PHP-6-5 cut-usefulness, 341 train / 232 test candidates):
    majority 0.552 · logistic(5 feats) 0.927 · GNN 0.974** (final = best, train→
    1.000, stable after an lr-decay fix).  **Reproduces — and slightly strengthens
    — the MLX flip** (0.92 vs 0.88 there) in the Rust-native stack: on asymmetric
    families a constraint-graph GNN beats intrinsic cut features.
  - Three more Burn gotchas hit + fixed: a manual `#[derive(Clone)]` silently
    freezes training (use the derive's id-preserving Clone); per-graph SGD is too
    noisy on small variable-size graphs (mini-batch the loss-sum over graphs); and
    late-epoch instability needs an lr decay.
  - **GPU backend option (Burn Metal/wgpu) added + measured — CPU wins at this
    scale.** `--features gpu` swaps the backend to Apple-Silicon Metal (one cargo
    feature; model code unchanged via Burn's backend abstraction).  Both backends
    give the **identical 0.974** test accuracy (correctness confirmed across
    backends), but 300 epochs: **CPU/NdArray 178 s vs GPU/Metal 472 s (~2.6×
    slower on GPU)** — the textbook "kernel-launch overhead dominates many tiny
    ops" regime (~50-node graphs).  So CPU is right for the current de-risk; the
    GPU win is at scale (large g-PHP / big batches / expert-iteration rollouts).
    Infra is in place for when that arrives.
- **● GNN wired into the warm loop — end-to-end cut reduction, veripb-VERIFIED
  (2026-06-21).** The trained GNN now drives cut selection inside `gmi_loop_warm`.
  Design keeps `gmi.rs` burn-free: the loop takes an **injected scorer closure**
  `Fn(cons, x*, candidates) -> scores` (`refute_scored`); the `gmi_train` bin
  supplies one that builds the constraint graph and runs the trained Burn GNN.
  - **End-to-end refutation cut counts (held-out g-PHP-6-5, top-50%/round, all
    paths veripb-checkable; the GNN-policy proof spot-checked → VERIFIED):
    add-all 29.0 · logistic 20.5 · GNN 17–19 (avg)** — the GNN selector makes
    ~10–15 % smaller proofs than the hand-feature logistic and ~35 % smaller than
    add-all, on instances it never trained on.  The representation edge
    (prediction 0.97 vs 0.93) translates to fewer cuts in the actual loop.
  - Soundness is structural + checked: the scorer only changes *which* valid CG
    cuts are kept; the exact Farkas closes and VeriPB verifies (same path as the
    logistic policy).  The policy half of the Aristotle / AlphaZero-for-cutting-
    planes loop, realized end to end in Rust.
  - **Next:** expert iteration — search for shorter cut sequences than the current
    policy finds, retrain the GNN on them (proof size = deterministic reward),
    iterate; and scale (larger g-PHP, where the GPU backend starts to pay off).
- **◐ Expert iteration + CPU scaling — search headroom is real but one ExpIt round
  doesn't capture it; workload is training-bound (2026-06-22).** `gmi_train`.
  - **ExpIt de-risk (positive):** best-of-K stochastic rollouts (GNN scores +
    exploration noise) around the imitation policy find **shorter** proofs than the
    greedy policy on every held-out g-PHP instance — **best-of-12 15.6 vs
    deterministic 17.0 cuts (~8 %)**.  So search beats the one-shot policy: ExpIt
    has headroom.
  - **ExpIt iteration (negative):** relabel each train instance on its shortest
    rollout's Farkas support → retrain → compare in-loop.  Across runs the
    retrained policy does **NOT** beat imitation (ExpIt-GNN 16.4 vs imitation 15.3;
    16/19 elsewhere) — it's slightly worse.  Honest causes: the recorder logs only
    *selected* candidates under topfrac<1 (biased targets, not all-violated), tiny
    data, and a single iteration with no value head.  A real win needs proper MCGS
    (visit-count/value targets over the constraint-set DAG) + unbiased candidate
    recording, not naive best-of-K relabel-retrain.
  - **CPU scaling:** data-gen parallelized cleanly (rayon, pure engine, **0.1 s**).
    Rollout-level parallelism does NOT help this config: it's *training-bound* (two
    sequential GNN trainings ≈ 6 min of an ~11 min run), and the GNN forwards are
    tiny so parallelism overhead dominates.  **std::thread over burn-ndarray's
    internal rayon oversubscribed catastrophically (87 min); rayon-outer composes
    (one pool, no disaster) but nets ~no speedup (11:44, ~1.7 cores avg).**  Added
    `NTR/NTE/EPOCHS` env sizing.  Real multi-CPU payoff needs much larger
    (rollout-dominated) instances, or building burn-ndarray without `multi-threads`
    so the outer pool doesn't nest — future.

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
