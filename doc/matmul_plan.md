# Fast matrix multiplication — native-representation local search (matmul track)

*Started 2026-07-02. Goal: an efficient SAT solver for the Heule
matrix-multiplication challenges built on our connection-method (NNF-matrix)
solver — exploiting the native non-clausal representation instead of the CNF
explosion, and bringing local search to the connection method.*

---

## 0. The problem

Finding a way to multiply 3×3 matrices in r products = solving the **Brent
equations**: bit tensors α, β, γ (over GF(2) for the SAT version) with

    XOR_m  α[m][a,b] ∧ β[m][c,d] ∧ γ[m][p,q]  =  δ_{b,c} δ_{a,p} δ_{d,q}
                                     for all (a,b,c,d,p,q) ∈ [3]^6

i.e. **729 cubic XOR equations over 27·r variables** (r=23: 621 vars, 27
equations with RHS 1 — the "type-3" terms). Best known: r=23 (Laderman 1976);
lower bound 19 (Bläser). **r=22 is open in both directions** — mod-2 SAT at
r=22 would be a genuine discovery (and liftable candidates exist: HKS lift
ℤ₂→ℤ via Gröbner bases, failing only rarely); UNSAT would prove no integer
scheme with 22 products exists.

**What Heule–Kauers–Seidl established** (SAT'19 arXiv:1903.11391; JSC 2021,
the two source papers for this track):
- CNF encoding: 621 base vars + Tseitin (pooled AND pairs, XOR chunks of 3)
  → **26,541 vars / 117k clauses**. Instances + generator:
  github.com/marijnheule/matrix-challenges (cloned at `matmul/challenges/`,
  gitignored).
- **CDCL fails on both SAT and UNSAT sides** (their diagnosis: avg backtrack
  level >100; runtime ~exponential in ABL). Confirmed here: kissat UNKNOWN at
  60 s on our n3r23 CNF *and* on their challenge-1 instance; kissat needs
  41.6 s to prove even 2×2 r=6 UNSAT (the rank-7 bound, 776 vars).
- **Local search (yalsat) wins, but only with structure**:
  - *Method 1*: hardcode a random pairing of the 27 type-3 terms into
    products (4 products get 2 terms, 19 get 1 → 81 unit clauses) +
    streamliners (zero-or-two occurrence; "one factor matrix nearly zero, one
    factor a single entry" for single-type-3 products) → yalsat solves in
    seconds-to-minutes; a few CPU-hours per new scheme end-to-end (most
    random pairings don't extend).
  - *Method 2*: fix **414/621 (2/3)** base vars from a known scheme, search
    the remaining 207 → a neighbor in **~1 s**.
  - Campaign: ~35 CPU-years → **>13,000 mutually inequivalent new
    23-schemes** (SAT'19; the public DB snapshot later reached 17,376,
    up from 4 known). None compresses to 22.
- **Living record 315 + Kaporin F_p obstruction (2026-07-15)**:
  PLinOpt data-dir SLPs for the identical rational-48 matrices
  checker-verify at 315 (<104,4>+<75,1>+<110,21>) — 26 below the
  paper's 341 (artifact ahead of text; zkML B.5 dual-cites with
  snapshot date). shiftmin: L/R have ZERO label-slack; P needs
  inline-group emission (v3) for a verdict. Kaporin complex-48:
  i and sqrt(3) exist in Goldilocks+BabyBear but CBRT(2) DOES NOT
  (2 not a cubic residue; 3|p-1) -> his 2^(-5/3) instance cannot
  instantiate over either base field (needs F_p^3) — an F_p
  obstruction parallel to MSY's R-obstruction; class-level question
  open (144/192 algebraic forms unpublished; author contact in
  kaporin/NOTES.md). Pivot begun: F_p witness-gen benchmarking of
  the 315 networks (bench315 codegen).
- **Adds-record probes COMPLETE (2026-07-15)**: 341 (DPS, Appendix
  B, PLinOpt kernel route) survives everything: our checker-gated
  365 (their instances, sweep 3); 8h cse48 storm (flat); 40 dyadic
  sandwiches (>= 422 — dyadic re-gauging strictly adds shift mass);
  60 signed-permutation sandwiches (>= 371 — coefficient-preserving
  orbit moves are protocol noise). Sandwich action bug found+fixed
  en route (c' = P^-T c R^T in our convention; engine teleports had
  been silently failing verify). Remaining levers: BP-style
  cancellation-aware CSE; the F_p reframe (shifts free, scheme
  freedom from our pools). Phantom 329 retracted same morning.
- **Moves paper (2026-07-14, doc/matmul_moves_paper)**: the methods
  paper — space anatomy (disconnection certificates), move field
  guide M-1..M-10 with toy examples, campaign techniques + verdicts
  table, classical-algorithm mapping (BFS=closures, IDDFS=cfloor,
  greedy-best-first=chase, B&B=floors pruning; UCS=min-altitude
  escape possible; A* blocked on admissible h but repair-radius h
  is admissible-within-k; minimax n/a; MCTS/MCGS best fit with
  gmi_mcgs scaffolding). Unifying layered-multigraph formulation.
- **pursue9/10 descent program (2026-07-14)**: K-M protocol
  reproduced and iterated. pursue9 monotone-from-naive: F2 arm
  64->53 in 10 min then stalled (single trajectory; 1 reduction in
  3.8h/3.3B flips); Goldilocks arm STERILE (0 reductions in 448M
  flips, skeleton lambda included). pursue10 = K-M Algorithm 2
  (frontier pool + length-limited restarts) + solved flips +
  periodic closing quench: F2 descends 64->55 in 69s at 4 threads,
  4h x 12-thread run chasing 47 now. STRUCTURAL INSIGHT: F2
  naive-descent works by birthday collisions in a 2^16 factor
  space; over 2^64 fields the factor space is effectively infinite
  — collisions never, closings need coplanarity generic states
  lack -> naive-descent is small-characteristic magic; F_p flip
  search needs scheme seeds (our storms' regime). Explains why
  HKS/K-M pipelines do not transfer to proof fields directly.
- **Widenings batch COMPLETE (2026-07-14 00:00)**: all four stages
  negative, all exhaustive where finite. A: BabyBear 4x4 repair
  k<=6 rigid (matches Goldilocks). B: ALL 30 census seeds k<=9
  rigid over Goldilocks (210 ladders, ~1.7M subsets each). C: 4x4
  k=7 EXHAUSTIVE — 73,629,072 subsets, 4.5 h, zero completions ->
  DPS-48 is k<=7 locally rigid over Goldilocks (any 47 shares at
  most 41/48 terms). D: m31 arm, 10 seeds, 790K walks/seed, 1.52M
  distinct 23-landings, zero RECORDP — third proof field, same
  emptiness. Exclusion zone now: bands 26/28/30 x three fields
  (~31M walks, 4.4M landings) + repair radius 9 (3x3, 30 seeds x
  2 fields) / 7 (4x4 G) / 6 (4x4 BB).
- **Commutative record targets (priced 2026-07-13)**: 3x3<=20 comm
  = 7.0% whole-pipeline (4.65%/unit — highest value-per-space on
  the board; Rosowski 21 is constructive, not optimized; LBs leave
  mid-teens room); 5x5<=80 = 10.6%; 7x7<=200 = 12.7% (~rank-47
  class). Tooling: commutative flip graphs (2506.22113); our
  engine could grow a flipC mode (mixed-variable bilinear forms,
  symmetrized Brent verify). Today's comm ceiling (t=7 tiles):
  5.3% — smaller than exponent wins, stacks with them.
- **Multilinear directions (from 2026-07-13 discussion)**: (a)
  symmetric flip mode (cyclic trace(ABC) invariance, the M-P
  record technique) for flip23p/flip48p; (b) order-4 fused
  triple-product constructor — CAVEAT (2026-07-13): standard
  attention's softmax between QK^T and .V breaks fusion; exact
  targets are nonlinearity-free chains: LoRA (x.B.A),
  linear-attention variants (Q.(K^T V) — associativity IS their
  design), factored projections. Wins under degree-3 AIR gates if
  rank4 < r1+r2 — pursue8-style build; (c)
  commutative base-tile carve-in written into zkML section 3
  (Rosowski 21 @ 3x3, 85 @ 5x5; base-tile-only). Border rank: not
  a constraint-count lever at fixed sizes.
- **Field-novelty screen COMPLETE (2026-07-13)**: the ~215K pooled
  F_p landings span 170 distinct rank-type multisets; 114 match no
  DB pattern; after dedup vs our 81 Z-classes + 467 Q-dyadics (63
  known-novel multisets), **63 truly-new field class-patterns**
  remain (G: all 63, 22,554 schemes; BB: 36 of them, 11,135 — BB
  subset of G, no G/BB separation). One-way certified (rank-triple
  invariants); novelty is vs the known corpus — field-SPECIFICITY
  (no Q counterpart exists) is a separate open question. The
  (2,2,2)x4 motif is conserved across all pool classes (inherited
  from the 4n census seeds). Reps + multisets:
  new23/fieldnovel_multisets.txt; screen: screen_fieldnovel.py.
- **Day-2 repair ladders + hi-30 arm COMPLETE (2026-07-13 11:26)**:
  all negative, all exhaustive. 3x3 repair k=5..9 over BOTH fields:
  1,687,257 subsets/field, zero completions -> mm23 seed is k<=9
  locally rigid over Goldilocks AND BabyBear (delete 39% of the
  scheme, no 22-rebuild exists). 4x4 repair k=5 (1.7M) + k=6
  (12.3M) Goldilocks: zero -> DPS-48 k<=6 locally rigid (no 47
  within replacement-distance 6). hi-30 arm, 10 seeds x 1200 s:
  5.0M walks, 107K landings, zero RECORDP (histogram peaks 26-27).
  Next widenings: repair ladders from OTHER class reps (rigidity is
  seed-specific), 4x4 k=7 (73.6M, ~3.5 h), BabyBear 4x4 ladder,
  m31 arms, novelty screen of the 122K pooled landings.
- **Rank-22 two-arm portfolio COMPLETE (2026-07-13 00:26)**: no 22
  over Goldilocks or BabyBear. 30 seeds x 1200 s x both arms;
  G (hi 26): 9.98M walks, 1.93M distinct 23-landings, 61.9K pooled;
  B (hi 28): 11.45M walks, 743K landings, 60.7K pooled; zero
  RECORDP. Band verdict: hi 26 out-lands hi 28 ~2.6x throughout.
  Next options: 3x3 repair ladder k=5..9 (cheap), hotter bands
  (hi 30+ small arm), field-novelty screen of the 122K pooled
  schemes, m31 arm, pursue8-repair on exotic pool members.
- **Challenge-3 sweep (2026-07-12, `matmul/chk_type3.py`)**: no scheme
  with a type-3-free summand exists in the known+ours corpus — 29,514
  schemes checked (29,290 dbcache + 4 classics + our 53 + replica4 31
  + new23 48; verify-gated, monomials from brent_equations rhs=1).
  Sharper regularity than HKS stated: min type-3 per summand is
  EXACTLY 1 in all 29,514 — every rank-23 scheme has a boundary
  summand doing one unit of real work; none reaches min>=2 either.
  Attack path if wanted: anf portfolio on their MM-23-no-type3.cnf.
- Challenges (no cash, open since 2019): (1) solve pairing-only instances
  without streamlining — yalsat gets 5/10; (2) prove one of 10
  hardcoded-pairing instances UNSAT; (3) find a scheme with one product
  having no type-3 term; (4) **r=22**.

## 1. The thesis — why native representation should win

The CNF costs local search a 43× variable blowup (26,541 vs 621) — flips
wander through Tseitin auxiliaries that aren't real decisions. The Brent
system is natively **ANF** (XOR of AND-monomials), which is exactly a
non-clausal NNF-matrix our connection-method engine can represent (and a
2-level special case of general NNF local search). Native advantages:

1. **State = the 621 real bits.** Flipping var v touches exactly the 81
   equations containing it; the monomial toggles iff its two partners are 1.
   Incremental make/break is O(81) trivially, vs yalsat pushing flips through
   ~26k aux vars and 117k clauses.
2. **Structured moves CNF-SLS can't express.** The system is *tri-linear*:
   fixing two of (α,β,γ) makes it **linear in the third** — exact GF(2)
   Gaussian closure (our `xor_gauss` machinery) as a *move* (ALS mod 2),
   not just blind bit flips. Pairing/streamlining become native constraints
   or frozen bits, not clause soup.
3. **The connection-method research question** (the novel part): the matrix
   view of the ANF system suggests local search over *satisfaction
   scenarios* (per-equation choices of which monomials are on, conflicts =
   connections on shared variables) rather than assignments — path-space
   SLS on the NNF matrix. Nobody has done SLS on the connection method.
4. **Witness verification is absolute and free** — a found scheme is checked
   against the Brent equations in microseconds (`matmul/brent.py
   verify_bits`, independent of any solver). No proof machinery needed on
   the SAT side.

## 2. De-risk results (2026-07-02)

Built `matmul/brent.py` (generator/verifier/CNF emitter) and `matmul/sls.py`
(native-ANF WalkSAT prototype, pure Python):

- **Generator verified against two historical schemes**: Strassen 2×2×2 r=7
  and Laderman 3×3×3 r=23 both give **0/729 violated** (Laderman support
  153/621, matching the paper's ~160 mean). Single-bit flips break them.
- **Native SLS finds a valid 2×2×2 r=7 scheme from scratch** in 13.8k flips
  (~0.1 s at 154k flips/s in *Python*), verifier-confirmed.
- **3×3 r=23 from scratch stalls** (best 78/729 unsat at density-0.25 init)
  — expected: yalsat needs structure too (its from-scratch regime is
  minutes at ~10⁶–10⁷ flips/s; Python is ~10⁴/s at this size).
- **Seeded repair (method 2) is instant natively**: fix 414/621 at Laderman,
  random-init the rest → **solved in ~200–550 flips (<10 ms in Python)**,
  vs ~1 s for yalsat-on-CNF. First direct evidence for the representation
  thesis (caveat: Laderman is isolated — completions re-find Laderman; the
  paper's 1 s includes hunting *different* neighbors from richer seeds).
- **Repair-range curve is soft, not a cliff** (3 trials each, 90 s cap,
  Python): fix=350 → solved (1–4k flips); fix=300 → solved (6k–140k);
  fix=250 → stuck at **4–16 unsat of 729** after ~4M flips; fix=200 → ~15;
  fix=150 → ~18–35. The horizon sits at ~320 free bits in Python; a
  1000×-flips Rust engine + real noise/restart schedules attacks a soft
  wall, not a hard one. (All solved completions land back on Laderman.)
- Naive pairing-only (method 1, no streamliners) stalls in Python at ~229 —
  consistent with challenge 1 being the hard open regime (yalsat: 5/10 in
  minutes = 10⁸–10⁹ flips; needs the Rust engine).

## 3. Plan — rungs with gates

- **R1 — Rust native-ANF SLS engine. ● BUILT + thesis validated
  (2026-07-02).** `src/anf.rs` + `src/bin/anf.rs`: CSR cubic-ANF system,
  WalkSAT/SKC + probSAT policies, Luby restarts, frozen-var seeding/pairing
  modes, rayon portfolio, independent from-scratch verifier gating every
  claimed solution; Laderman/Strassen embedded as verified bit-strings
  (transcription-proof, guarded by tests). 5/5 tests green.
  - **Throughput**: 0.4–3.6 M flips/s single-core by regime (below the 10⁷
    aspiration — candidate break-scans dominate; caching is a known v2
    lever) — but wall-clock already wins big (below), because one native
    flip ≈ many CNF flips of work.
  - **Seeded-repair curve (single core)**: fix=414 → **284 flips, <1 ms**;
    fix=300 → 5 ms; fix=250 → 60 ms–1.5 s (8/10 seeds ≤1.5 s, two stuck at
    best=1–2); **wall now at fix≈200** (best 5/729 after 207 M flips/120 s).
    Python prototype's wall was fix≈250; Rust moved it ~50 bits deeper.
  - **yalsat A/B on identical semantics (our CNF + unit-fixed seeds), same
    machine**: fix=414 → 0.04–0.18 s (paper-consistent ~1 s regime); but
    **fix=300 and fix=250 → TIMEOUT at 300 s** — instances the native
    engine solves in **5 ms / 60 ms**: a ≥5,000× wall-clock gap.  The
    native representation extends the *repair horizon* — the quantity that
    controls how far from a known scheme search can travel.  (Caveat: our
    Tseitin CNF is ~25 % bigger than HKS's pooled encoding; that doesn't
    explain 4+ orders.)
  - **Scheme "diversity" was product-reordering**: fix=250 completions at
    Hamming 6/6/18 from Laderman are all VERIFIED but collapse to **1
    distinct scheme after summand sorting** (`matmul/canon.py`) — i.e.
    Laderman with permuted product slots.  Laderman's isolation holds
    exactly as HKS found ("Laderman 0 new"); genuinely-new schemes need
    richer seeds (Smirnov/Oh from the Linz DB: 561/94-scheme
    neighborhoods) or method-1 cores — R2.
  - Policy probes at the fix=200 wall: probSAT (cb 2.5) best=11, walksat
    noise 0.35 → 7, 0.1/luby-2¹⁶ → 8 vs default 0.2 → 5 — the wall is a
    difficulty transition, not a tuning artifact.  (Restart-from-best
    perturbation added — `--pert`, default 0.06 — no breakthrough at
    fix=200 either.)
  - **The pairing regime is a different policy point — probSAT + density
    0.1 is the unlock.** Control experiment: Laderman's own type-3 core
    (93 frozen bits, profile 4-4-4-4, extendable by construction —
    `matmul/inst/core-laderman.freeze`).  Default WalkSAT/0.25 floors at
    best **193** (worse than unconstrained from-scratch!); density 0.15 →
    69; **probSAT cb 2.5–3.5 at density 0.10 → SOLVED in 3–4 ms** (5.5–8.6
    k flips).  Density ≈ the free-support of completions ((153−93)/528 ≈
    0.11), and probSAT's break-only dynamics fit the frozen-ON landscape —
    consistent with yalsat (probSAT-family) being HKS's winner.  Frozen
    handling itself verified by a consistency ladder (all-621-fixed solves
    at init; 400/250-fixed + core solve in 85/1.7 k flips).
  - **Regime → config duality**: close-repair (seeded ≥250 fixed) wants
    WalkSAT/0.25 (fix=250: 60 ms vs probSAT's 14.5 s); pairing/from-scratch
    wants probSAT/0.10 (random pairing: best 10 vs WalkSAT's 65).  Random
    pairings mostly don't extend (paper-consistent); official challenge-1
    cores imported (`matmul/import_core.py`, γ-transpose validated).
  - **Official challenge-1 result (2026-07-02): 5/10 cores SOLVED — equal
    to yalsat's published record — at ≤120 s × 10 threads each** (probSAT
    cb 2.5, density 0.10, seed 3):
    | core | native | yalsat here (300 s cap, 1 seed) |
    |---|---|---|
    | 2-2-2-2-A | **0.069 s** ✓ | TIMEOUT |
    | 4-4-4-4-1 (Laderman-core) | **0.019 s** ✓ | 0.62 s |
    | 2-2-2-3-4 | **11.0 s** ✓ | — |
    | 2-2-2-4-B | **30.5 s** ✓ | — |
    | 2-2-2-2-D | **24.5 s** ✓ | — |
    | 2-2-2-2-{3,B,C}, M, 2-2-2-4-A | best 2/2/1/4/6 of 729 | M: TIMEOUT |
    All 5 solutions VERIFIED against our Brent system; the A solution
    additionally **kissat-confirmed against their exact CNF**
    (`matmul/check_their_cnf.py` plants our 621 bits as units → s
    SATISFIABLE).  All misses are near-misses (1–6 unsat) — final-mile
    candidates for R2 (Gauss closure, longer budgets); note HKS pose these
    as SAT instances but which 5 are yalsat-solvable is instance-specific,
    and near-miss ≠ guaranteed-SAT.  Aggregate throughput peaked at
    **10.1 M flips/s** (10 threads) — the ≥10⁷ gate met in aggregate, open
    single-core.
  - **Same-machine yalsat baseline complete** (single-seed, default
    config, 300 s cap): fix300 ×3 + fix250 ×3 + plain + chal1-A + chal1-M
    → all TIMEOUT; chal1-4-4-4-4-1 → SAT 0.62 s.  Honest caveats: 1 seed,
    1 core, no tuning; the paper itself reports 5/10 in "a few minutes",
    so treat per-instance timeouts as "slower here", not "cannot".
- **R2 — structure moves. ● closure + discovery pipeline landed
  (2026-07-02).** Design note: with (α,β) fixed the γ-system **decomposes
  into 9 independent 81×23 GF(2) systems** (equations partition by γ's
  (p,q) index; likewise per (a,b) for α, (c,d) for β) — and since every
  equation contains exactly one group of each tensor, **a fully-consistent
  single-tensor closure solves the whole instance**, and each closure call
  is monotone (solved groups satisfy all their equations; inconsistent
  groups are left untouched).
  - **Built**: `closure_group`/`closure_tensor` in `src/anf.rs` (u64-row
    RREF, frozen-aware via RHS-substitution, free vars keep current values)
    + an injected-hook seam in the SLS (`--closure-every N`, cycling
    γ/α/β — same injection idiom as gmi's scorer).  Tests: wiping any one
    tensor of Laderman and closing reconstructs a full VERIFIED scheme;
    frozen bits never move; monotonicity asserted.  7/7 tests green.
  - **Challenge-1 beyond yalsat: 7/10 official cores solved** (was 5/10
    without closure; yalsat's published record is 5/10): closure converts
    B (96 s) and **C (0.090 s)**.  Remaining 3/M/2-2-2-4-A float at best
    3–4.
  - **Seed bank**: 24 schemes fetched from the Linz DB and
    verifier-confirmed (4 classics + 20 across distinct rank patterns;
    `matmul/seeds/`, agent-built; `.tab`/`.exp` γ conventions determined
    empirically = transposed).  DB indexes 17,372 schemes total.
  - **Neighborhood discovery works and compounds** (all counts =
    distinct-after-summand-sort, the paper's own metric): from Smirnov at
    nfix=414, 20/20 completions re-find Smirnov (few-%-yield regime, as in
    the paper); at **nfix=300, 20 runs → 3 new schemes** (supports
    139–141); hop 2 from a found scheme → **3 more new** + walks back to
    Smirnov.  `matmul/walk.py` productizes this (pool of seeds+finds →
    random hops → canon-dedupe → archive `matmul/found/`), every accepted
    scheme independently re-verified.
  - **Walk pipeline demo: 138 new schemes in 365 s — 3 s/scheme,
    single-threaded** (`walk.py --minutes 6 --nfix 300 --runs 8`; pool =
    24 seeds, archive `matmul/found/`, every accepted scheme re-verified;
    `cat found/*.bits | canon.py` → 138 read / 0 INVALID / 138 distinct).
    The rate *accelerates* as the pool diversifies (last 24 schemes in the
    final 14 s).  vs the paper: method 1 ≈ CPU-hours/scheme; their
    Smirnov-walk ≈ 85 CPU-s/scheme.  Honest scope: distinct-after-
    summand-sort = the paper's *neighborhood* metric; de-Groote
    inequivalence (their 17k headline metric) is stronger and not yet
    implemented — so these are new-to-our-archive, not yet certified
    new-to-the-literature.
  - Method-1 (random pairings + closure, from scratch): **0/30 pairings
    extended** at 20 s × 10 threads — paper-consistent ("only very rare
    random pairings extend"; their few-CPU-hours/scheme reflects burning
    through many).  With the walk at 3 s/scheme, method 1 is a diversity
    side-channel (longer budgets / streamliners), not the pipeline.
  **Gate (≤ minutes/new-scheme on M4 Pro): met — 3 s/scheme.**
  Stretch (beyond yalsat on challenge 1): **met — 7/10** (600 s retry on
  the last three queued).
- **R3a — de-Groote equivalence + novelty audit. ● landed (2026-07-02).**
  `matmul/equiv.py`.  Key derivation: in the **(α, β, γᵀ)** representation
  our convention equals HKS's, the group acts as the clean cyclic sandwich
  (PAQ⁻¹, QBR⁻¹, RC̃P⁻¹), and every summand-match constraint is **linear**
  in the 27 unknown bits of (P,Q,R) — so exact equivalence = rank-triple-
  pruned backtracking + incremental GF(2) RREF + nullspace enumeration +
  invertibility + full multiset check.  Invariant fingerprint (multiset of
  sorted summand rank-triples + pair-sum rank-triples) prunes first.
  Self-test: 12 random group elements preserve the Brent equations and are
  found equivalent-with-witness; laderman vs smirnov inequivalent.  Two
  Python-int gotchas fixed en route (interned-small-int `is` in rank;
  bit-order in inverse).
  - **Audit (2.6 s total): 162 schemes (138 found + 24 seeds) → 152
    fingerprints → 153 exact classes.  The 138 walk finds = 129 distinct
    de-Groote classes, NONE equivalent to any seed.**  One fingerprint
    collision was exactly-separated (walk-00134 vs db-i106… — invariants
    equal, schemes inequivalent), vindicating the exact stage.
  - **Novelty CERTIFIED at the database level (2026-07-02,
    `matmul/novelty.py` + `db_rank_patterns.txt`).** Decoded the DB's
    dir-name legend by constraint-solving over our 20 dir↔scheme pairs:
    dirs are letter-coded multisets of per-summand rank types — letters
    refine sorted rank triples by slot (a=(1,1,1); b/d/j=(1,1,2);
    c/g/s=(1,1,3); e/k/m=(1,2,2); f=(1,2,3); n=(2,2,2); w=(2,2,3));
    coarse level suffices for an absence test.  Extracted all **302**
    patterns from the DB index (count matches the site).  Unknown letters
    (h/l/p, 8 patterns) treated as wildcards — conservative, never
    falsely certifies.  Control: Laderman's pattern {13×(1,1,1),
    6×(1,1,3), 4×(2,2,2)} is absent from all 302 — correct, the classics
    live outside the found-dirs and HKS note their finds never reached
    Laderman's type.  **Result: 5 of the 138 walk finds
    (walk-00029/00091/00106/00108/00122) have rank patterns matching NONE
    of the 302 dirs and NONE of the 4 classics, and are pairwise
    inequivalent (10/10 exact checks) → five schemes provably
    inequivalent to every scheme in the published HKS database** (rank
    patterns are de-Groote invariants).  Residual assumptions: the
    dir-name legend fit (20-sample-consistent) and index completeness
    (302 = their stated count).
  - **Full-DB crawl SETTLED it (2026-07-03, agent; ~25 min):** the 133
    undecided finds needed 132/302 dirs; the site's single `schemes.tgz`
    (43 MB, all **17,376** .tab files) was used instead of ~12 k requests,
    validated byte-for-byte against a live-fetched probe.  **0/17,376
    parse failures** (C-transpose conversion, every file
    `verify_bits==0`); **13/13 seed-anchor controls** recovered
    byte-identically from their predicted dirs; the 5 certified-new
    controls got 0 candidate dirs, as predicted.  Verdicts
    (`matmul/novelty_verdicts.csv`): **85 finds EQUIVALENT to DB schemes**
    (77 distinct; witnesses returned) — expected, the walk was DB-seeded —
    and **53 finds NEW vs the entire database**.  **Hardened
    unconditionally**: all 17,376 DB schemes fingerprinted; the 53 NEW
    finds (×6 S₃ variants) have **zero fingerprint matches anywhere** —
    the verdict no longer depends on the dir-name legend at all.  The 53
    are pairwise inequivalent (53 distinct classes) and inequivalent to
    the 4 classics (earlier seed audit) ⇒ **53 new 23-multiplication
    mod-2 schemes vs everything published**, from one 6-minute walk.
  - **● All 53 LIFTED to ℤ (2026-07-03, `matmul/lift.py`) — 53/53, zero
    failures, every one exactly ℤ-verified.**  Lifting as **sign-SAT**
    (our twist vs HKS's Gröbner route): sign bits per support
    coefficient, a term's sign = XOR of its three sign bits, each
    integer Brent equation = an exactly-(k−rhs)/2 cardinality over its
    k covering terms; per-product scaling broken by fixing the first
    α/β support signs.  Tiny CNFs (~2 k clauses), kissat solves each in
    ms.  Controls: all 4 classics lift + ℤ-verify.  Result: **53 new
    integer {−1,0,+1} schemes** (`matmul/lifted/*.txt`), valid over any
    commutative ring — the same object class as Laderman's.  (En route:
    a parity bug caught by the exact ℤ-verifier failing on exactly the
    27 delta equations — the verify-everything discipline paying off.)
- **R3b — r=22 probes** (challenge 4 infra): `matmul/drop22.py`
  (drop-a-product repair seeds) + plain r=22 attacks with closure.
  - **Campaign wave 1 (2026-07-03, `matmul/campaign22.py`): 210 bounded
    attacks (45 s × 6 threads each; drop-a-product over all 162 schemes +
    10 % plain), best floor 1/729, 0 solutions.**  The near-miss shell is
    **broad, not concentrated**: floor ≤2 reached 32× across ~30 distinct
    (scheme, drop) combos spanning every family (floor 1 hit 9× across 8
    schemes; laderman twice, drops 18/19); nfix barely matters (mean
    floors 4.9–6.0 for 250–320; plain 7.1).  Reading: the r=22 polytope
    has a dense violation-1 shell reachable from any wounded 23-scheme —
    consistent with either SAT-needle or min-violation-1 UNSAT; the floor
    pinning at exactly 1 across 9 independent diverse hits leans
    UNSAT-ish, but 210×45 s is tiny compute vs HKS's 35 CPU-years — no
    conclusion.  Wave-2 design (not yet run): save floor-≤2 assignments
    (`anf --emit-best`), then a **finisher** per near-miss — identify the
    violated equation, exhaustive 1/2/3-flip repairs over its 69 vars,
    closure contradiction counts — which either finds a solution or
    characterizes the obstruction (which equations pin, local rigidity).
  - **Wave 2 done (2026-07-03): 146 honest attacks, best floor 2, no
    solution.** By mode: PAIR22 (r=22 pairing, n=63) min 9 / median 13 —
    pairing-from-scratch is far from the boundary at these budgets;
    PLAIN (n=31) min 6 / median 7; **drop-multi (n=52) min 2 / median
    13** — multi-cover drops do reach deep (six attacks ≤5) but the
    floors are genuine (post-finisher design), not artifacts.  Combined
    wave-1+2 verdict: r=22 remains open; the honest boundary sits at
    2–6 violated equations across attack families; further waves need
    either much larger budgets or a qualitatively new idea (e.g.
    restructuring moves that re-cover multiple type-3 terms at once).
  - **● Finisher ran (2026-07-03) — obstruction identified, UNSAT-lean
    RETRACTED.** `anf --emit-best` added (chain-best assignment surfaced
    through the portfolio); floor-1 states collected
    (`matmul/nearmiss/`); `matmul/finisher22.py` (incremental
    flip-prober + per-tensor exact closure diagnostics).  Findings:
    - Every analyzed floor-1 state violates **one type-3 (delta)
      equation, covered 0×** — the state is "26/27 type-3 terms
      covered"; per-tensor closure fails by exactly 1 contradiction row
      each; **rigid to radius 3** (≈1.3 M structured flip-sets per
      state, none repairs).
    - Cause, verified: **every floor-1-producing drop removed a product
      that was the sole cover of exactly one type-3 term** (laderman
      d18, db-i4 d9, walk-00031/124 d9 all solely-covered term (0,1,0) —
      which is why independent near-misses all violate the same
      equation; walk-00094/115/130's drops solely-covered (0,2,0),
      (1,1,1), (0,2,1)).  The repair patches every even equation but
      cannot re-manufacture the missing odd term (needs an exact
      triple-intersection in some product).
    - **Consequence: the "dense floor-1 shell" of wave 1 is an artifact
      of drop-a-product seeding, and the earlier weak UNSAT-lean is
      withdrawn.**  The unbiased r=22 signal is the plain-attack floor
      (best 8/729).  If a wave 2 runs: plain attacks + drops of
      multi-type-3-cover products (forcing genuine restructuring) +
      lower nfix; single-cover drops are structurally pinned at ≥1.
- **R3c — connection-method path-space SLS. ○ built, measured, NEGATIVE
  (2026-07-03).** `matmul/pathsls.py`: a correct path-space local search
  on the ANF matrix — state = per-equation scenario (ON-monomial set,
  parity-consistent) + a blocker var per OFF monomial (the disjunct the
  path takes); **connections** = vars forced 1 by one equation's scenario
  and 0 by another's blocker; moves = re-blocker, scenario swap, and
  parity-preserving pair add/remove (the size-changing move the first
  version lacked); frozen bits as permanent force-counts.  Correctness
  proven: init-from-solution ⇒ 0 connections; incremental force counts +
  conflict set + parity invariants all consistent after 200 k moves.
  - **Equal-budget A/B (Python vs Python, same machine/wall):**
    | regime | assignment-SLS | path-SLS |
    |---|---|---|
    | 2×2×2 r=7 scratch (30 s) | SOLVED 0.48 s | best 4 connections |
    | 3×3 fix=414 (60 s) | SOLVED 0.02 s | best 60 |
    | 3×3 fix=300 (90 s) | SOLVED 0.12 s | best 51 |
  - **Diagnosis** (why, not just that): the connection objective
    (#conflicted vars) collapses badly — one conflicted var hides
    force1×force0 pending repairs and each path move shifts one force
    count by ±1, so there is no gradient; and the Brent matrix has
    *dense* sharing (every var in 81 equations, 69 vars/equation), so
    connections are everywhere and path rerouting is myopic.  One
    assignment flip re-evaluates all 81 incident equations at once —
    exactly the quotient path moves can't take.  Path search pays where
    connections are sparse/local (first-order tableaux, unification);
    dense ANF is its worst case.  The native-representation win of this
    track came from ANF structure (cheap flips + tri-linear closure),
    NOT from path-space search.
  - Scope: naive-but-correct prototype, three move classes, light
    tuning; a cover-space or hybrid formulation could be tried, but an
    orders-of-magnitude gap in every regime doesn't invite it.  Gate
    ("any slice where it wins") — **not met; negative documented.**
- **R4 — the r=22 campaign** (moonshot, gated on R1–R2). Seeded long-range
  exploration (the 17k-scheme DB as seeds, low fixing fractions), pairing
  variants at r=22 (27 = 5×2+17×1 or with triples), drop-a-product +
  repair probes. Bounded, checkpointed background runs
  ([[bound-and-watch-background-compute]]). Also viable: challenge 3
  (no-type-3 product) as a nearer novel target.
- **R5 — the 4×4 campaign (2026-07-03, running).** Records: 47 mod 2
  (AlphaTensor 2022 = KM flip graphs), **48 over ℤ** (AlphaEvolve
  May 2025, de-complexified by Dumas–Pernet–Sedoglavic
  arXiv:2506.13242), lower bounds mid-30s.  **Tier 2 (the record shot):
  generate new 47-classes mod 2 by seeded walks, sign-SAT lift-test
  every one; a liftable 47 beats 48 over ℤ.**  Tier 1: 4×4 additive
  complexity via the CSE pipeline.
  - Infra: lift/slp/walk generalized to dims (`--dims`), 3×3 regression
    clean; the anf engine needed nothing (dims-parametric since R1).
  - Seeds (agent, verified): `seeds4/alphatensor47.bits` (support 450)
    + `seeds4/km47-0.bits` (support 677; the only machine-readable KM
    4×4×4-47) — canon-distinct; `seeds4/alphaevolve48.json` (exact
    dyadic rationals, denominators to 1/8 ⇒ mod-2 undefined; Tier-1
    seed only, needs coefficient-aware CSE).
  - **Baseline: both known 47s are NOT ±1-liftable (sign-SAT UNSAT)** —
    the reason 48 is the ℤ record, and the campaign premise: every NEW
    47-class is a fresh liftability ticket.
  - Calibration: 4×4 seeded repair fast to ≥nfix 1350/2256 (13 ms);
    first walk launched at nfix 1150 (≈ 3×3's sweet-spot fraction).
  - **Rust engine + waves 1–2 (2026-07-04).** `src/flip.rs` (parallel
    descend, frontier pool, rank-adaptive seek; 3×3 control: 3,430
    distinct rank-23s/min = ~1000× Python).  Wave 1 (2h×10t, naive
    restarts): 43.2B flips, ONE rank-49 landing.  Wave 2 (5h×10t,
    frontier): **40,238 distinct rank-49 schemes** — and zero at 48.
    Measured funnel: 64→50 trivial, 49 an enormous plateau harvested at
    ~8 landings/s, **49→48 is the wall** (≈3×10⁵ rank-49 visits ×
    10⁵-attempt seeks, no merge pair ever sampled).  Random flips don't
    engineer two-slot-equal pairs at this depth; wave-3 lever = GUIDED
    descent (objective: factor-multiset concentration / targeted
    pair-equalization), the track's recurring lesson that guidance, not
    scale, breaks walls.  The 40k rank-49 corpus is itself an asset
    (4×4 CSE targets; novelty pool pending the GL(4,2) equiv port).
  - **Guided descent (v3, 2026-07-04): harvest ×6, wall intact.**
    Agreement-steered flips (row-score: +1 per 1-agreement pair, +200
    per mergeable pair; Metropolis) + deterministic merges: 20-min probe
    → **6,990 distinct rank-49s** (~6× wave-2 rate) and 65,791 landings —
    but **zero mergeable pairs ever formed at rank 49** (min rank still
    49).  Reading: myopic 1-step agreement steering reaches 49 fast but
    cannot engineer 2-agreements there; plausibly reproducing the
    literature's own wall (KM's first flip paper reports 49 for 4×4×4;
    47 required later techniques).  Wave-4 candidates, in order:
    **(a) targeted pair equalization** — pick a 1-agreement pair (i,j),
    slot o: equalizing needs s[i][o]⊕s[j][o] expressible as an XOR chain
    of flip-reachable factors — an exact GF(2) reachability question our
    stack is built for (guidance-by-linear-algebra fused into search);
    (b) KM's symmetry restriction (symmetric flip graphs shrank 5×5
    dramatically); (c) brute cloud scale.  The 47k+ rank-49 corpus is a
    standing asset regardless.
  - **Wave 4 (certified equalization, 4h×10t) + STRUCTURAL VERDICT
    (2026-07-04).** try_equalize_merge (solve for a 1/2-flip XOR chain
    that forces a merge; transactional) layered on the restored deep
    seek (a 50× starvation bug that stalled descent at 52 was found +
    fixed; regression guard `descends_below_trivial_rank` added).
    Result: 33,125 more rank-49 schemes, **zero sub-49 landings**.  The
    decisive probe (`flip_analyze.py`, 80 rank-49 landings): **pairwise
    shared-factor histogram is 100% at agreement 0 — every rank-49
    landing is a flip-graph SINK** (no two summands share any factor, so
    NO flip applies and equalization has no 1-agreement pair to promote).
    This is the documented Kauers–Moosbauer obstruction: the low-rank
    flip graph is dominated by isolated vertices; reaching 47 needs
    rank-increasing escape through different basins + their symmetric-
    flip-graph machinery + AlphaTensor-scale compute (years of field
    effort).  **Honest stop for the pure-flip-descent line at 4×4.** What
    stands: a fast verified parallel flip engine, the lift-lottery
    design, ~100k verified rank-49 schemes (a 4×4 CSE / novelty asset),
    and the record-TYING additive-complexity results at 3×3 (doc/
    matmul_adds_paper.md).  Genuine routes to 4×4 records from here are
    research-scale: (a) KM symmetric flip graphs; (b) rank-increasing
    random walks (not greedy descent) spending time at rank 50–51 where
    the graph is connected; (c) cloud-scale search.
  - Missing before 4×4 *novelty* claims: GL(4,2) port of equiv.py (same
    cyclic-sandwich linearization, 48-bit unknowns); canon-level
    distinctness gates the lift loop meanwhile.  Strassen² CSE baseline
    208 greedy vs 198/165 structured (structure-aware CSE = upgrade
    lever).
- **R6 — exact input-side minimizer (2026-07-04, `matmul/sidemin.py`)**.
  Sun's 56 (arXiv:2604.27645) = 13+13+30 with *chain-covering* input
  sides (all 23 rows are values of one addition chain) — a structure
  pair-extraction CSE cannot represent (our v1/v2 plateaued at 58 =
  14+14+30 on his rep).  `sidemin.py` solves the side subproblem
  *exactly*: minimum #(binary ± adds) so that one chain over the 9
  input cells contains every distinct multi-term row up to sign.
  Method: iterative deepening on helper count h; normal form = greedily
  cover every creatable target (pool is monotone ⇒ complete by an
  exchange argument), branch only on helper insertion at closure
  fixpoints; at h=1 the helper must directly complete a target
  (enabling-set restriction).  Helpers may be arbitrary integer vectors
  (doubling allowed) — strictly more general than Sun's pure/aux1
  certificate model, so our h-exhaustion is the stronger impossibility.
  Gates: micro-optima 5/5; Sun's U (nt 12, h*=1 → 13, 3 nodes) and V
  (nt 11, h*=2 → 13, 11 nodes) reproduced with his pure/aux1
  impossibility certificates, 0.3 s total; every chain replay-verified;
  every sign model Z-verified (z_verify returns bad-equation COUNT —
  an inverted assert was caught immediately by the Stapleton run).
  **Results (exact A/B sides + heuristic C, 24 Z-verified sign models
  each)**: sun56 rep → **56 = 13+13+30 tied by our own pipeline**
  (24/24 models); cr58-cn122 → **56 = 13+14+29 — ties the world record
  on a DIFFERENT de Groote class** (≢ sun56 by equiv.py; Perminov's
  published count for that scheme was 58); cr58-cn119 → 57 (published
  58); cr58-cn120 → 57 = 13+16+28 and cn120 ≡ sun56 — so **C = 28
  exists inside Sun's own class** while sides 13+13 exist on Sun's rep;
  mws59 → 58 (published 59); our i106/i106b/i107 orbit-best reps →
  **59 = 15+15+29 each** (our three classes tie the old MWS record);
  stapleton60-orbitbest → 60 = 16+16+28.  Side costs were sign-model
  invariant on every rep tested.  **Next: the 55-hunt** — orbit sweep
  inside the hot classes (Sun's, cn122's, cn119's) scoring
  exact-sides + heuristic-C: sides-optimal (13+13) and C-optimal (28)
  representatives coexist within one class; a single rep with both
  gives 54–55 and the outright record.
- **R7 — Rust floor scanner (2026-07-04, `src/floors.rs` + bin
  `floors`)**.  Port of orbitscan.py's exhaustive table machinery:
  GL(3,2) as 9-bit ints, exact GF(2) chain-covering side cost
  (512-bit-bitset pools, closure + helper IDDFS), three 168² tables
  per S3 variant built rayon-parallel, min-plus scan, candidate
  emission for Python Z-rescoring (`--emit-cands`), `--floors-only`
  sweep mode (A+B tables only).  **Parity: line-for-line with the
  Python scan on sun56 — all six floors (26/28/29/26/29/28),
  est-bests (56/57/57/56/57/57), candidate counts
  (432/216/324/444/252/216)** after making the C-greedy tie-break
  insertion-ordered like CPython's dict+max.  One non-bug chased to
  ground: "budget cells" were actually max-slack exhaustion cells
  (true cost ≥ nt+4) — the Python reference stores the same
  lower-bound values *silently*; renamed `open_cells`, semantics
  documented (floors stay sound).  **Speed: full 6-variant class scan
  5.4 s at 10 threads vs tens of minutes–hours in Python (~300×)**;
  DB-wide floor sweep (17,376 classes) now ~a day, was ~a year.
  New floor facts from the first Rust runs: cn119's class floor is
  **27** (variants 2/4 — 55 there needs sides 27 + C 28); cn122's
  floor 27 (v0/2/3/4); **mws59's class floor is 29 and their rep's
  sides 14+15 = 29 already sit ON it** (57 in that class needs
  C ≤ 28; best C seen there 29).  Tests: GL=168+inverses, micro
  optima, Sun identity sides 13/13 + Brent gate + bits round-trip;
  ignored release gate = full sun56 v0 (floor 26 / est 56 / 432
  cands); suite 309/309.  Also fixed a pre-existing
  unused-assignment warning in flip.rs (build back to zero
  warnings).
- **R8 — Rust Z-rescorer + full-Rust exhaust pipeline (2026-07-04,
  `src/zrescore.rs` + bins `zrescore`, `floors --emit-sides`)**.
  Per-candidate exact pipeline in Rust: sign-model enumeration =
  lift.py's encoding on in-process CaDiCaL (XOR3 term bits, binomial
  exactly-(k−r)/2, α/β gauge units, blocking clauses; every model
  z_bad-asserted); exact signed side-min = sidemin.py's algorithm on
  [i16;9] (arbitrary ℤ helpers, exact memo keys); greedy C = slp.py
  v1 ported bit-for-bit on the deterministic pass (str()-key
  ordering + insertion-ordered first-max).  Gates: 6 reference
  totals reproduced exactly; sun56 m0 sides nt12+h1/nt11+h2;
  Z-negative control; suite 313/313.  ~0.28 s/scheme at 24×300
  effort (~150× Python) and parallel across candidates.
  **55-hunt milestone — slim-sides exhaustion of BOTH new 56-classes:
  every rep with GF2 sides ≤ 28 in the entire orbits of cn119's
  class (4,320 reps) and cn122's (6,480) exact-Z-rescored in 11.3
  min: best = 56, no 55.**  With the earlier Sun-class exhaust
  (1,728 reps ≤ 27): all three known 56-classes have NO 55 in the
  slim-sides regime; remaining routes are C ≤ 26–27 on fat-sides
  reps (needs C lower bounds / exact C) or other classes (DB-wide
  floor sweep, now ~1 day in Rust).  Cross-validation: Python
  orbitscan, running blind in parallel, produced cn122 v3/v4/v5
  floors 27/27/28 and cn119 v0/v1 28/28 — exactly the Rust
  predictions, with matching candidate counts; both Python jobs then
  stopped as superseded.
- **R9 — C-side lower bounds via exact XOR-SLP SAT (2026-07-04/05,
  `matmul/cxlb.py` v1+v2) + solver landscape + DB floor sweep.**
  cxlb: "do k XOR additions suffice for the 9 C-forms over the 23
  products?" as SAT (FSK-flavored; unit-vector inputs collapse bit
  semantics to one base literal + AND-guarded prior terms).  UNSAT at
  k ⇒ C_Z ≥ k+1 (mod-2 reduction) — the sound closure tool for the
  fat-sides 55 windows.  v2: value-lex symmetry breaking on adjacent
  independent steps (sound by bubble-swap; monotonicity selftest),
  abstract XORs materialized as Tseitin or NATIVE CMS x-lines,
  portfolio solving, --window K + --drat.  Soundness catch: v1's
  dead-step elimination broke monotonicity in k (odd padding can
  need a dead step) — could have corrupted a completed descent; none
  completed, nothing published affected; removed.
  **Solver shootout on the live sun56 k=29 boundary** (23,867 vars /
  84k clauses): kissat 600 s + 1800 s ✗, cadical 600 s ✗,
  cryptominisat 615 s ✗, z3 word-level QF_BV + ordered pairs 600 s ✗;
  v2 (SB + portfolio + native XOR) 900 s ✗ under sweep load.  CMS's
  Gauss cannot engage through AND-guarded parities — solver shopping
  is not the lever; boundary certificates cost hours each (clean-
  machine reruns pending).  Lean/grind: category error (proof
  automation, not search); Lean's role = LRAT certification of final
  boundary UNSATs.  cvc5 ≈ cadical backend + overhead (not run;
  bounded by cadical's row).  **Calibrated C-floors (verified SAT
  witnesses + resisting boundaries): sun56 cell GF2-min ∈ {29,30};
  cn120 cell ∈ {27,28}.**  Production plan for window closure:
  enumerate the distinct C form-sets inside each class's fat-sides
  window, one long DRAT-certified UNSAT@27 (or @26) per form-set —
  weekend-scale, certifiable.
  **DB-wide floor sweep** (Rust, --screen-nt 13, class-parallel ×10
  after the row-parallel version proved load-starved): all 17,376
  classes; at 69% had already surfaced **195 classes with sides
  floor ≤ 27 — all exactly 27, none below** (mirrors cn119/cn122;
  Sun's 26 still unique).  Follow-up per candidate class:
  emit-sides 28 + zrescore (minutes each).
- **Later options**: MCGS/learned policy over restart seeds / move classes
  (ties back to the neural track); UNSAT side (challenge 2) via our proof
  machinery — a *different* project (algebraic/symmetry lower-bound
  reasoning, not enumeration).
- **2026-07-15 — machine-aware F_p pivot.** (a) **Living adds record is
  284, not 315**: DPS data-dir `4x4x4_48_accurate` triple checker-counts
  ⟨80,4⟩+⟨68,8⟩+⟨108,16⟩; Brent over ℚ under the calibrated convention;
  Goldilocks codegen (slp284/bench284r) field-gated; 4–5% faster witness
  gen than 315 at n=64/1024. zkML paper B.5/C updated. (b)
  **machinecost.py**: machine-cycle scorer — shift dyadics, small-odd
  chains, delayed reduction (the F_p mult-add-fusion analogue: (lo,hi)
  accumulators, one reduce per output; eligibility = P-DAG over
  {+,−,×2^k}). Lane verdict: SWAR/NEON batches *across tiles*, so lanes
  don't reorder scheme rankings (BB 4×32 ≈2–3×, Goldilocks ≈parity).
  (c) **machopt.py** exponent-relabel storm (product prescales + P-wire
  relabels, plateau-shaped objective, ℚ-gated): 48 restarts incl.
  constructive column-flatten init → **no gated improvement**; mechanism
  identified: 16 blockers are shared-wire conflicts on output lines —
  pure relabels provably insufficient; **v2 move = wire duplication**
  (compute w and 2^k·w separately, ~1 shift each). Complementary fact:
  converged2k/ours P is already 16/16 delayable at higher op count —
  attack from both ends. Also queued: delayed-reduction Rust bench (El
  with dual-accumulator type) to convert model wins into measured ones.
- **2026-07-15 — benchzk verdicts.** n=256 BN254 Groth16: naive 16.8M
  constraints, setup 99 s / prove 119 s; strassen 5.8M constraints but
  433 s / 389 s — **the density inversion measured at scale**. All
  rank-48 configs (matlv 0,2,3,4) and even naive --full OOM'd: n=256
  Groth16 sits at this machine's ~32 GB ceiling (RSS-guard kills logged;
  swap/compression = the 20% CPU stretches). New `--full` scenario mode:
  witness-gen + NTT fwd/inv at the proof-domain size + setup/prove/verify
  phase table (n=64: naive domain 2^19 NTT 22/20 ms setup 1.0 s prove
  1.2 s verify 0.23 s; rank48 matlv2 domain 2^18 NTT 10.6/11 ms setup
  7.1 s prove 7.8 s). Goldilocks-STARK twin = natural next build.

- **2026-07-15 (evening) — benchmark harvest + calibrated-search verdicts.**
  NTT field pricing measured (single-core, gated): Goldilocks 1.6–2.6×
  over BN254-Fr per core; ark's parallel FFT 4.7× at 2²². n=64 --full
  sweep: strassen still density-benign at depth 6 (prove ≈ naive on
  2.2× fewer constraints); rank-48 matlv-2 optimum stands. n=256 final:
  rank-48 unmeasurable on 64 GB at ANY matlv (≤3 swap-balloon 190+ GB
  footprint; matlv-4 >46 GB resident in synthesis) — needs ~128 GB.
  n=4096 witness gen measured: rank-48 83 s vs blocked 246 s, ratio
  0.34 ≈ 0.46×(48/64) — compounding lands as predicted. ourslane
  (18 variants, checker+machine-score gated): incumbent 705.2
  (Rt_Lt_Ptt_g2) stands; g2 gauges dominate; runner-up 721.9. bpcse
  fraction-blindness on accurate_R classified (parser, not search).
  Paper: Appendix B measured-NTT table; Appendix C n=256 verdict,
  --full pipeline table, n=4096 row, machine-cost subsection. NEXT:
  delayed-reduction implementation in bench (model vs silicon);
  fraction-aware bpcse; longer ourslane converge on R_Ptt_Lt_g2.

- **2026-07-15 (night) — model vs silicon: the flip refuted, cleanly.**
  bench705 (gen_slp315.py --delayed-P codegen: unreduced (lo,hi) limb
  pairs, bound-tracked negation constants, one combine/output;
  field-gated on 20k tiles): 284-scalar 282 ns/tile, ours-scalar 331,
  ours-DELAYED **461** — 1.63× slower where machinecost said 0.94×.
  Mechanism: dependent-chain constants price latency; tiles run at
  throughput (OoO overlaps 48 independent mul+reduce chains — hides
  exactly what deferral skips; delayed path forfeits ILP to longer
  chains + 2× register state). Verdict: at tile granularity
  machine-optimal ≈ op-minimal; **284 = measured-fastest rank-48
  witness-gen path**; delayed reduction stays where it's standard
  (long all-positive dots — gates + wins in benchdr). Paper subsection
  finalized as the full model→search→refutation arc. Task #27 closed.

- **2026-07-15 (late) — BabyBear NEON arm (bench_bb).** Montgomery
  32-bit + explicit NEON 4-lane mont-mul (vmull pairs, vshrn, vmin
  cond-sub); El-generic 284 codegen reused verbatim over Bb/Bb4;
  4 gates. Measured ns/tile: naive 53.5→20.0 (2.68× lanes), 284
  177.4→76.8 (2.32×). Cross-field: BB-NEON naive 9.9× over
  Goldilocks-scalar naive; 284 path 3.7×. Autovectorization only
  1.47× on mul-bound path — intrinsics required. Economics shift:
  cheap 32-bit muls make adds dominate → naive beats 284 at BB tile
  level 3.8× → rank-48 recursion crossover is field-dependent
  (later over BB). Paper: Appendix C machine subsection extended.
  Possible next: BB recursion bench (locate the BB crossover), BB
  NTT curve for the B table, M31/circle-STARK arm.

- **2026-07-16 — BB arm completed: NTT curve + recursion crossover.**
  benchntt_bb (two-adicity 2^27, generator 31, Montgomery, 4 gates):
  5.8–6.8× over Goldilocks per core (0.118 s vs 0.68 s @ 2^22; word
  width + halved cache footprint compound), ~9.4× over 1T BN254-Fr.
  bench_bbr (methodology-matched to bench284r, gates at 16/64):
  rank-48-vs-blocked 1.61/1.31/0.97 at n=64/256/1024 — **BB crossover
  at n≈10³ vs n≈64 over Goldilocks** (two recursion levels later).
  Paper: Appendix B table now 4 fields; Appendix C closes the
  field-dependence story quantitatively. Field-comparison summary
  (G vs BB vs M31 incl. two-adicity-1 / circle-STARK obstruction)
  given in chat; M31 arm would require a circle FFT (new build).

- **2026-07-16 — PLONKish/AIR gate port (benchair): density tax ERASED,
  measured.** Plonky3 uni-stark over BabyBear (Poseidon2 + two-adic
  FRI). Two AIRs over the IDENTICAL 48-col trace (one 4×4 tile/row;
  commitment work held constant): naive gate vs rank-48 gate = the
  284 SLP over AIR expressions (El for the Expr type; slp284g.rs
  unchanged — codegen now spans u64/u32/blocks/NEON/constraints).
  Gates: honest accepted, tampered rejected, both AIRs. Prove times:
  16.9/16.9, 56.1/56.8, 224.1/230.0 ms at 2^12/2^14/2^16 tiles —
  **parity within 3% where Groth16 charged 17.6×**. Scope note: flat
  tile gate doesn't WIN either (in-constraint naive materializes
  nothing; 48-vs-64 quotient mults trade vs 284 adds on a mul-cheap
  field); mult-count pays in memory-mediated precompile chips /
  block-recursive layouts where cells track op count. Paper: Appendix
  C erasure paragraph + Reading lever upgraded to measured. Next
  candidates: memory-argument precompile chip (multi-table), Goldilocks
  AIR variant, depth-1 block-recursive AIR.

- **2026-07-16 — benchmetal: Apple-GPU tile witness-gen hits the memory
  wall.** gen_msl.py = sixth codegen target (284 SLP → MSL; 32-bit-only
  Montgomery via mulhi + parity-carry; wrong hardcoded NP caught by the
  host assert before any GPU work). M4 Pro, 2^22 tiles, gated
  bit-for-bit vs CPU: naive-looped 0.95 / naive-unrolled 0.90 /
  rank48-284 0.93 ns/tile — an apparent 284 win was a loop-indexing
  spill artifact, killed by the unrolled control. ~0.9 ns/tile ≈
  213 GB/s of ~273 = bandwidth-bound: on GPU the gate arithmetic is
  free, bytes are the currency (22× NEON-naive, 59× scalar-naive).
  Three substrates, one law: mults (G-CPU) → adds (BB-CPU) → bytes
  (GPU); converges with the AIR verdict (reduce cells/rows). Paper
  updated (machine subsection). Possible next: Metal NTT stage kernels.

## 4. Discipline

- Every claimed scheme re-verified by the independent verifier; every A/B at
  equal wall-clock on this machine; long runs capped + watched.
- Scheme novelty: dedupe by sorted-summand form first; full de Groote
  equivalence (|G| = 168³·6 mod 2) only if we get to claiming *inequivalent*
  new schemes.

## 5. References

- Heule, Kauers, Seidl. *Local Search for Fast Matrix Multiplication.*
  SAT 2019. arXiv:1903.11391.
- Heule, Kauers, Seidl. *New ways to multiply 3×3-matrices.* J. Symbolic
  Computation 104 (2021) 899–916. (NSF PAR 10302523; arXiv:1905.10192.)
- Laderman. Bull. AMS 82(1):126–128, 1976. (23-product scheme; transcribed
  mod 2 in `matmul/brent.py`, symbolically verified.)
- marijnheule/matrix-challenges (instances, encoder, challenges 1–4).
- Scheme database: algebra.uni-linz.ac.at/research/matrix-multiplication/.
- Bläser. *On the complexity of the multiplication of matrices of small
  formats.* J. Complexity 19(1):43–60, 2003. (rank ≥ 19.)
