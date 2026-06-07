# Multi-session project: polynomial-size VeriPB proofs via extension variables

## Goal

Produce VeriPB-verifiable **polynomial-size** UNSAT proofs for
cardinality-flavored problems where pure RUP and pure cutting-planes
hit the at-most-1-from-pairwise-mutex wall (see
[`pbp_emission.md`](pbp_emission.md)).

Primary targets, in order:

1. **PHP-N-M for any N > M ≥ 3** — known polynomial proofs exist
   (Cook 1976; Buss 1987 without extension; Heule et al via PR).
   Validate that our infrastructure produces VeriPB-checkable
   polynomial proofs.
2. **RoundRobin n16_d13** — the original goal of this whole thread.
   The cardinality argument (120 matches > 104 slots) requires the
   same extension-variable machinery.
3. **(Stretch) Generic cardinality structure detection** — auto-detect
   pigeon-style + at-most-one structure in arbitrary CNF inputs and
   emit appropriate cutting-planes-with-extension proofs.

## Background

### Why we need this

Our current emission options:

| Format | Strength | RoundRobin n16_d13 |
|--------|---------|---------------------|
| Cover cert (`--emit-cover`) | Sound matrix-native, verifier-side hardness = problem hardness | Prover 37s, verifier hangs (CSP equiv to original) |
| DRAT (`--emit-drat`) | RUP-only; bounded by resolution lower bounds | Sound prefix, incomplete (resolution insufficient) |
| PB-RUP+pol (`--emit-pbp`) | Adds cutting-planes, but bounded by what pure-CP can express | Sound prefix, incomplete (cardinality wall) |
| PB+extension (this project) | Cook's polynomial-size proof family | Target: polynomial-size verified proof |

### Why extension variables are the unlock

For PHP-N-M and tournament-style problems, the polynomial CP proofs
use **auxiliary variables** that name partial sums or partial-prefix
indicator functions. Without aux vars:

- Pairwise mutex `~x_i + ~x_j >= 1` ∀ i<j cannot derive at-most-1 by
  pure pol+div (best is at-most-⌊K/2⌋ for K vars).
- The cardinality bound that closes the UNSAT proof requires
  aggregating "exactly one X per row" style constraints, which
  pairwise mutex doesn't directly give.

Cook 1976 introduces y_{p,k} = "pigeon p is in some hole in [1..k]"
and derives the counting argument arithmetically with these aux vars.
The resulting proof is O(N·M) constraints.

### Where VeriPB fits

VeriPB supports extension via `red` rules with witness substitutions
that introduce fresh variables. The witness defines how to extend
an assignment to set the new variable consistently. From
[GN21](https://gitlab.com/MIAOresearch/software/VeriPB#how-to-cite-veripb):

> Substitution redundancy (the basis of VeriPB's `red`) is
> equivalent to PR (Propagation Redundancy), which is polynomially
> equivalent to extended resolution.

So in principle, VeriPB has the expressive power for Cook-style
PHP proofs. The challenge is **encoding the proof correctly** —
choosing the right aux vars, the right witnesses, and the right
sequence of `pol`/`rup`/`red` rules.

## Phase plan

### Phase 1 — Research & hand-crafted PHP-4-3 prototype  *(1–2 sessions)*

**Goal**: a hand-written, VeriPB-verified, polynomial-size proof of
PHP-4-3 using extension variables. Establishes the technique.

**Tasks**:

- [ ] Read Cook 1976 ("A short proof of the pigeonhole principle
      using extended resolution") and Buss 1987 if available.
      Extract: exact extension-variable definitions, the
      cutting-planes derivation pattern.
- [ ] Read the VeriPB papers/docs on the `red` rule with witness:
      [GN21](https://link.springer.com/chapter/10.1007/978-3-030-72013-1_22)
      and follow-ups. Confirm how to introduce fresh vars via
      witness.
- [ ] Find example VeriPB proofs that use extension variables (look
      in `~/projects/veripb/tests/instances/correct/` for hints).
- [ ] Hand-write a PHP-3-3 or PHP-4-3 proof using extension vars.
- [ ] Verify with `veripb --cnf <cnf> <pbp>`.
- [ ] Document the technique step-by-step in
      `doc/cook_php_walkthrough.md`.

**Success criterion**: `veripb --cnf php_4_3.cnf php_4_3_cook.pbp`
reports `s VERIFIED UNSATISFIABLE`, with proof size O(N·M).

**Risks**:

- VeriPB's `red` rule may have different mechanics than the pure
  extended resolution Cook uses. May need to adapt the proof structure.
- The witness substitution for fresh aux vars is the most non-obvious
  part; may take several iterations.

**Estimated effort**: 4–8 focused hours.

### Phase 2 — Parametric PHP-N-M generator  *(1–2 sessions)*

**Goal**: Python script `tools/cook_php_proof.py N M` that emits
CNF + Cook-style PBP for arbitrary PHP-N-M with N > M.

**Tasks**:

- [ ] Translate the hand-written PHP-4-3 proof into a parametric
      template.
- [ ] Test on PHP-5-4, PHP-6-5, PHP-7-6, PHP-10-9.
- [ ] Measure: generator time, proof size, VeriPB verification time.
- [ ] Confirm polynomial scaling (proof size O(N·M), verification
      polynomial in proof size).
- [ ] Update `doc/cook_php_walkthrough.md` with the generated proof
      template + measurement table.

**Success criterion**: Table showing polynomial growth in proof size
and verification time across PHP-N-M for N up to ~20.

**Estimated effort**: 4–6 focused hours.

### Phase 3 — RoundRobin adaptation  *(2–3 sessions)*

#### Phase 3.A findings (done)

**Structural analysis** (`tools/cook_php_proof.py` adapted from PHP):

RoundRobin n16_d13:
- **120 matches** (pigeons), **13 days** (holes).
- **Per-pair at-most-1** (pair-day mutex): each match plays in at most
  1 day. Same as PHP's per-hole pairwise structure.
- **Per-day at-most-8** (via team-day mutex aggregation): each team
  plays at most 1 match per day; 16 teams = 16 slots; 1 match = 2
  team-slots; so matches/day ≤ 8.
- UNSAT by cardinality: 120 > 13×8 = 104.

**The key wall**: Cook's PHP recursion derives at-most-1 per Q-hole
through Q-mutex clauses. For RR we'd need at-most-8 per Q-day, which
isn't derivable by the same recursion.

**Two viable adaptations**:

1. **Team-reduction recursion (Cook-style)**: remove 1 team at each
   step. After 1 reduction: 15 teams × 13 days, 105 matches, ≤ 7
   matches/day (= 105 / 15). After 2 reductions: 91 matches in
   13 days × 7 = 91 — just barely unsat boundary. Wouldn't crack
   n16_d13 with simple team-removal.

2. **Aux-var cardinality (one-shot)**: introduce y_{t,k} = "team t
   plays SOME match on day k" via extension. Then:
   - `sum_t y_{t,k} ≥ 2 * matches_day_k` (each match counts twice).
   - `sum_t y_{t,k} ≤ 16` (at most 16 teams).
   - Therefore `matches_day_k ≤ 8`.
   - Combined with sum of pigeon clauses ≥ 120, sum over 13 days ≤
     104: contradiction.

Approach (2) is more direct. Estimated proof size: O(n²·d) = O(13 ×
208) ~ a few thousand lines.

#### Phase 3 tasks

3.B: Hand-write RoundRobin n4_d2 Cook proof  *(small test case)*
- n=4 teams, d=2 days. 6 matches > 4 slots → UNSAT.
- Easier to debug end-to-end before scaling.

3.C: Build parametric RoundRobin Cook generator
- Approach (2) above: emit y_{t,k} aux vars + cardinality chain.
- Test on n4_d2, n6_d3, ..., scale to n16_d13.

**Tasks**:

- [ ] Analyze RoundRobin n16_d13's CNF structure precisely:
  - Variables: `x_{ij,k}` = "match (i,j) on day k". 120 pairs × 13 days
    = 1560 vars.
  - "Pigeon"-style clauses: each match plays on some day (120 clauses
    of arity 13).
  - "Mutex"-style clauses: each team plays ≤ 1 match per day (31,200
    binary clauses, one per (team, day, match-pair-conflict)).
- [ ] Identify the analog of Cook's extension variables for the
      double-pigeon-hole structure (matches in days, plus
      teams-per-day mutex).
- [ ] Generalize the PHP proof technique to two-level cardinality:
  - Inner: at-most-1 per (team, day) → at-most-⌊16/2⌋=8 matches per
    day.
  - Outer: sum over 13 days × 8 ≤ 104 ≤ total matches = 120 → ⊥.
- [ ] Hand-write the proof for a small RoundRobin instance (e.g.,
      n=4, d=2 → 6 matches > 4 slots).
- [ ] Parametrize and test on increasing n, d until n=16, d=13.
- [ ] Verify with VeriPB.

**Success criterion**: `veripb --cnf RoundRobin_n16_d13.cnf
roundrobin_n16_d13_cook.pbp` reports VERIFIED UNSATISFIABLE in
seconds.

**Risks**:

- RoundRobin's double-cardinality structure may need more aux vars
  than PHP. Proof size may be O(n³ · d) or worse — still polynomial
  but bigger.
- VeriPB may struggle with extension-rich proofs at this scale; would
  need to optimize the emission.

**Estimated effort**: 8–16 focused hours.

### Phase 4 — Integration with matrix-method prover  *(2–3 sessions)*

**Goal**: New `sat` flag (e.g., `--emit-cook-pbp`) that detects
cardinality structure in the input and emits the Cook-style proof
automatically, no manual configuration.

**Tasks**:

- [ ] Add CNF structure detection: identify pigeon clauses (long
      disjunctions of vars sharing some index) and mutex clauses
      (binary clauses with the structure `~v1 + ~v2`).
- [ ] Build a structure-classifier: is this PHP-shape?
      RoundRobin-shape? Generic-cardinality-shape?
- [ ] For each detected structure, dispatch to the appropriate
      Cook-style proof emitter.
- [ ] Add `--emit-cook-pbp FILE` flag in `sat.rs`. When set, attempt
      detection; on success emit the Cook proof. On failure, fall back
      to standard `--emit-pbp`.
- [ ] Test on the SAT competition benchmarks; tally how many UNSAT
      instances get cardinality-detected vs not.
- [ ] Document `--emit-cook-pbp` in
      [`pbp_emission.md`](pbp_emission.md) and the new
      `doc/cardinality_detection.md`.

**Success criterion**: `sat --emit-cook-pbp` produces VeriPB-verified
proofs for PHP-class and RoundRobin-class inputs in the benchmark
suite, with the detection running in < 1% of prover time.

**Estimated effort**: 8–12 focused hours.

### Stretch — Generalization & publication path  *(open-ended)*

Beyond Phase 4:

- Generalize to "cardinality + mutex" structures broadly (not just
  PHP and RoundRobin shapes).
- Compare proof sizes against state-of-the-art PB solvers (RoundingSat,
  Sat4j, Open-WBO).
- Write up the result for submission to a SAT competition / PB
  competition, or a workshop paper.

## Per-session checkpoint structure

Each session should start with:

1. Read the **previous session's last commit** + the project doc.
2. Confirm the state of the task list (`TaskList`).
3. Pick the next task; mark it `in_progress`.
4. Work the task; commit when done.
5. Update the project doc with measurements / findings.
6. Mark task `completed`; document any new follow-up tasks.

The project doc is the **single source of truth** across sessions.

## Reference material to gather (Phase 1 prep)

Papers to read or skim:

| Reference | Why |
|-----------|-----|
| Cook 1976: "A short proof of the pigeonhole principle using extended resolution" | The original polynomial-size proof technique |
| Buss 1987: cutting-planes PHP proof | Alternative without explicit extension |
| Gocht & Nordström 2021 (GN21): "Certifying parity reasoning efficiently using pseudo-Boolean proofs" | VeriPB's `red` rule semantics |
| Bogaerts et al 2023 (BGMN23): "Certified dominance and symmetry breaking for combinatorial optimisation" | VeriPB extension mechanics |
| Heule, Hunt, Wetzler: "Short proofs of the pigeon hole principle from solvers" | Practical SAT-solver PHP proofs |

Practical artifacts to inspect:

| Artifact | Why |
|----------|-----|
| `~/projects/veripb/tests/instances/correct/version3/*.opb,*.pbp` | Example proofs, particularly the redundance ones |
| `~/projects/veripb/proof_format_overview.md` | VeriPB rule reference |
| `~/projects/veripb/docs/` (if present) | Detailed VeriPB docs |

## Open questions to resolve in Phase 1

1. **Can VeriPB introduce fresh variables mid-proof?** If yes, what's
   the syntax? (Educated guess: `red` with substitution like
   `y -> (expression)`.)
2. **What's the precise PHP proof structure?** Cook's original is for
   extended resolution; VeriPB's `red` is closer to PR. The mapping
   may need adaptation.
3. **How large is the proof actually?** Cook's PHP-N-M proof is
   O(N·M) in extended resolution. The VeriPB-equivalent may be larger
   due to encoding overhead.
4. **Does RoundRobin's two-level structure need more aux vars?** PHP
   is single-cardinality (1 row per pigeon); RoundRobin is double
   (rows for matches, columns for (team, day) slots). The
   extension-variable scheme needs to handle both layers.

## Done definition (project complete)

The project is "done" when:

1. ✅ **PHP-N-M generator** (`tools/cook_php_proof.py`) produces
   VeriPB-checkable polynomial-size proofs for any N > M ≥ 2.
   Verified up to PHP-20-19 (144,408 lines, 119 ms verification).
2. ✅ **RoundRobin generator** (`tools/cook_rr_proof.py`) produces
   VeriPB-checkable proofs for all 8 official `RoundRobin_n*_d*`
   UNSAT benchmarks. **`RoundRobin_n16_d13` verified in 36 ms** from a
   2,946-line proof — the original goal.
3. ✅ **Documentation**: `doc/cook_php_walkthrough.md` covers
   construction, both PHP and RR adaptations, full measurement tables,
   and the recursive at-most-1 subroutine that unlocks RR.
4. **(Optional)** Multi-engine validation: VeriPB's own correctness
   (formally verified for the rule set per [BGMN23]) is the standard
   for SAT-competition acceptance. No additional external validation
   needed for this goal.
5. **(Stretch — Phase 4)** `sat --emit-cook-pbp` flag with CNF
   structure detection that auto-detects PHP / RR shape and dispatches.

**Phases 1, 2, 3 complete. The originally stated goal is met.**

Phase 4 (sat integration) and stretch generalization (auto-detection
of pigeon+mutex structure in arbitrary CNF) remain as follow-on
work.

## Stretch update — generic "embedded pigeonhole" generalization (done)

`tools/cook_card_proof.py` (and the native Rust port in
`src/cook_pbp.rs`) generalizes the PHP/RR Cook proof to **any** CNF
carrying an embedded pigeonhole — including **reshuffled / polarity-
flipped** encodings — detected automatically (no hand-coded family
knowledge):

- **Pigeons**: P variable-disjoint at-least-one clauses of equal arity S,
  with literals of *any* polarity (pigeon picks ≥1 of S slots).
- **Holes**: each hole = the P pigeon-literals for one slot, required to
  form a *complete* pairwise-mutex clique (holds ≤1). Recovered two ways,
  tried in order: **(A) component** — connected components of the
  cross-pigeon mutex graph (PHP, reshuffled fphp); **(B) aligned** — the
  s-th literal of each pigeon sorted by |var| (MVRoundRobin, whose
  team-capacity mutexes merge the component graph). Completeness verified
  before emitting; refuses otherwise.
- **P > S** ⇒ UNSAT, via the literal-level Step-1..4 Cook proof (per-hole
  recursive at-most-1 → Σ~l ≥ S(P−1); Σl ≥ P pigeons; combine → ⊥).

Results (VeriPB 3.0.2, `veripb <cnf> <pbp>`):

| family / instance | pigeons × holes | proof lines | recovery | verdict |
|---|---|---|---|---|
| PHP-12-11 (clean) | 12 × 11 | ~150 | component | VERIFIED UNSAT |
| MVRoundRobin_n14_d10_v2 | 91 × 20 | 1799 | aligned | VERIFIED UNSAT |
| MVRoundRobin_n16_d10_v2 | 120 × 20 | 2379 | aligned | VERIFIED UNSAT |
| MVRoundRobin_n16_d10_v3 | 120 × 30 | 3559 | aligned | VERIFIED UNSAT |
| MVRoundRobin_n20_d10_v2 | 190 × 20 | 3779 | aligned | VERIFIED UNSAT |
| harder-fphp-016-015 (reshuffled) | 16 × 15 | 221 | component | VERIFIED UNSAT |

MVRoundRobin is **resolution-hard** — cadical 3.0 times out at 600s on
`n14_d10_v2` (127,491 clauses), while the polynomial Cook proof verifies
in ~60 ms. This is the matrix method's differentiator: compact proofs
where resolution/DRAT is exponential.

Wired natively: `sat -b eff --emit-cook-pbp` detects the shape on the raw
CNF and emits the proof; `run_benchmark.py --verify-unsat-proof` tries it
first (closing the cover cert's "None gap" on structured UNSAT).

**Scope.** Covers **single-level** embedded pigeonholes — clean (PHP),
extended (MVRoundRobin), and reshuffled/flipped (harder-fphp).

## Two-level composed cardinality — cliquecoloring (done)

`tools/cook_cliquecoloring_proof.py` proves the **clique-coloring**
family, a two-level (clique-membership × coloring) cardinality structure
whose contradiction lives at the *composition*, not in either layer:

- N vertices × C colors (each vertex ≥1 color) and K clique-slots × N
  vertices (each slot ≥1 vertex); clique-edge + coloring clauses force
  the K clique vertices pairwise-different colors, K > C ⇒ UNSAT.
- The proof reifies `z_{i,v,c} = clique_{i,v} ∧ col_{v,c}` and
  `y_{i,c} = ∨_v z_{i,v,c}` (via `red`), derives the composed
  at-least-one (A) and at-most-1 (B), then runs PHP-K-C on `y`. The key
  trick: (A)/(B) become `rup`-checkable once intermediate lemmas
  (`T,U` for A; `N,Q` for B) are added so unit propagation cascades
  through the existential composition.
- Structure is read directly from the CNF (K largest-arity all-positive
  clauses = clique-membership; next = vertex-color), so no synthetic
  layout is assumed.

VeriPB-verified on all 3 curated instances:

| instance | K×N×C | proof lines | verdict |
|---|---|---|---|
| cliquecoloring_n14_k7_c6 | 7×14×6 | 29,719 | VERIFIED UNSAT |
| cliquecoloring_n32_k5_c4 | 5×32×4 | 45,693 | VERIFIED UNSAT |
| cliquecoloring_n26_k7_c6 | 7×26×6 | 94,315 | VERIFIED UNSAT |

This is the two-level analogue of RoundRobin's (team,day) generator; the
composed-PHP + rup-intermediate technique is reusable for other
clean two-layer cardinality families.

**Wired natively** (in addition to the Python reference tool): `src/cook_pbp.rs`
has `detect_clique_coloring` + `emit_clique_coloring`, so `sat -b eff
--emit-cook-pbp` emits clique-coloring proofs directly (detection runs
after PHP/RoundRobin/embedded-pigeonhole; the K largest-arity all-positive
clauses are clique-membership, the next N are vertex-color) and the
`run_benchmark.py` UNSAT-proof gate covers it. Verified end-to-end on the
tiny `n3_k3_c2` demo and all 3 curated instances via the binary.

## Still open — rphp (relativized PHP)

`rphp` is **not** confirmed tractable and may be a proof-system
*impossibility*, not just effort:

- The non-shuffled `rphp_p25_r25` has a clean disjoint pigeon→resource
  layer (25 arity-25 clauses) but the relativization's second layer +
  contradiction differ from clique-coloring and remain undecoded.
- The shuffled `rphp5_050/085` are heavily obfuscated (mixed-polarity
  at-least-one + permuted, on top of the 2-layer relativization).
- Crucially, **relativized PHP is designed to defeat counting
  arguments** — it may require exponential cutting-planes/extended
  proofs, in which case no compact VeriPB proof exists. Resolve that
  proof-complexity question before investing in a generator.
