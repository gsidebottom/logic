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
- **Rosowski tilechip MEASURED (2026-08-19, commit 4cac27b)**:
  commutative <4,4,4>=46 (Thm 2, verified over Z + BabyBear in
  matmul/comm/rosowski.py) prototyped in the benchair tilechip with
  lr_w=32 mixed A|B forms; all gates pass (selfcheck + honest +
  4 tampers x 3 schedules). Verdict: rosowski46/rank48 =
  0.95-0.98x at 2^14/16/18 — the 48-io-op floor pins the tile at
  96 rows, so sub-48 products buy nothing and the doubled form
  width is pure cost; rank-48 bilinear is the 4x4 geometry
  optimum (rank48/naive reproduced at 1.166-1.169x vs predicted
  1.167x). Amortized-40 shared-S rejected analytically: a shared-S
  memory read costs >= the compute row it saves. Commutative wins
  rows only when the floor stops binding: 8x8 projection
  Rosowski-316 -> 508 rows/tile vs naive 704 / Strassen^2-343 ->
  535 (matmul/comm/SUMMARY.md) — follow-up if tile size flexes.
- **2x2 calibration of the certified pipeline (2026-08-22)**:
  brent_2x2x6.cnf (776 vars / 2,880 clauses, rank one below the
  proven-optimal 7 of Hopcroft-Kerr/Winograd): hydra_satsuma in
  certified mode (GE-forced units ignored, so the certificate covers
  the input formula) — UNSAT in 21.9 s; composed satsuma-SR + kissat
  proof dsr-trim VERIFIED in-pipeline (56 s) AND by an independent
  dsr-trim run on the saved 59 MB binary SR certificate (56.4 s,
  forward checking). First end-to-end machine-checked UNSAT on a
  Brent instance: the rank-7 lower bound for 2x2 over F_2.
  brent_2x2x7.cnf control: SAT in 346 ms; witness verified (0/64
  Brent violations) and equal to Strassen under A->AJ, B->JB (the
  k-swap) with products relabeled — de Groote uniqueness in
  practice. Gate: matmul/r22/check_2x2.py (4 gates). Scale note:
  the 3x3 rank-22 leaves are the same object at 594 base vars / 729
  equations (vs 84 / 64) where the level-1 strata time out at 2 h.
- **3x3 rank ladder — direct CDCL cannot deliver lower bounds
  (2026-08-22)**: certified hydra_satsuma on brent_3x3x{r}.cnf
  (brent.py encoding, 27r base vars / 729 equations): r=1 1 ms,
  r=2-4 ~0.5 s (container-bound), r=5 1.5 s, r=6 19.9 s, r=7 487-530 s
  (dsr-trim VERIFIED in 1,232 s on a 1.29 GB binary SR certificate —
  proof checking now outweighs solving), r=8 pending (2 h bound); r=9,12,15,17,18,19,20 ALL
  TIMEOUT at 30 min. Per-product factor x13 (5->6), x27 (6->7) —
  matching the 2x2 ladder (r=4/5/6: 0.18/1.65/21.9 s, x9-13): fully
  free Brent instances grow ~x10-30 per product regardless of
  distance to the threshold, T(r) ~ 20 s * 13^(r-6) -> r=9 ~12 h,
  r=19 ~1e8 yr. So a certified UNSAT at rank 19 — which would lift
  the F_2 lower bound from Blaser's 19 to 20 (also for Z; not Q/C/F_4)
  — is not a compute question for resolution. <2,2,3> r=10 (160 base
  vars; the rank-11 control is SAT in 13 s, witness verified):
  TIMEOUT at 1 h -> per-variable extrapolation >= 1e8 yr for a direct
  rank-22 run. CryptoMiniSat (XOR recovery + in-search Gauss-Jordan):
  r=5 2.8 s, r=6 115 s (x41), r=7 INDETERMINATE at 15 min — parity
  reasoning cannot reach through the AND-gated XORs. Diagnosis: two
  obstacles. (1) parity-of-products: resolution is exponential on it;
  (2) INVISIBLE LINEAR SYMMETRY: satsuma breaks permutation symmetries
  only, while the GL_3(F_2)^3 sandwich mixes variables and is unseen
  — 168^3/6^3 ~ 22,000x left on the table, exactly what the
  Lean-licensed strata exploit by hand. Candidate native proof
  systems: Res(xor) (linear literals = XOR boxes in the matrix
  method), Polynomial Calculus / Grobner over F_2 with Nullstellensatz
  certificates a Lean tactic can check, and symmetry-native
  cube-and-conquer with Gaussian-elimination leaves (the equations
  are linear in gamma once alpha, beta are fixed). Decisive next
  experiments before building solver boxes: (a) XL/Grobner refutation
  degree growth on r=1..7; (b) canonical-(alpha,beta)+GE prototype
  growth factor on r=5..9. Scripts matmul/r22/ladder_3x3.sh,
  ladder_small.sh (self-regenerating CNFs); run records committed.
- **Two proof-system experiments (2026-08-22)** — which native
  inference could carry an F_2 rank lower bound? (a) EXACT degree-D
  Polynomial Calculus closure over F_2 (src/bin/pcxl.rs: Macaulay/XL
  fixpoint, multilinear Boolean ring): refutation degree of the Brent
  system at rank r is r=1 -> 3, r=2 -> 4, r=3 -> 5 (3.85M rows, 61 s),
  r=4 -> >= 6 (the degree-5 closure completes at 4.29M rows / 158 s
  without deriving 1); r=5,6 open at degree 4. PC degree = r+2 on the
  measured range with ~x100 cost per step: algebraic refutation scales
  WORSE than CDCL; rank 19 would need degree ~21 over 513 variables
  (~1e36 monomials). Singular's degBound std (matmul/r22/pcdeg.py) is
  not an instrument — claims degree 6 for r=1, times out at D=4 for
  r>=2. (b) Symmetry-aware span search (src/bin/spansearch.rs): a
  rank-r scheme = r rank-one 9x9 matrices alpha(x)beta whose span
  contains W = span{E_pq} (gamma = the coefficients); enumerate
  T = W + <extenders>, v_1 up to GL_3(F_2)^3 (13 orbits of the 261,121
  rank-one matrices), decide each cube by Gaussian elimination. Gate:
  2x2 r=6 UNSAT (1,123 cubes), r=7 SAT with a Brent-re-verified
  scheme. 3x3: r=9 UNSAT with 0 cubes (W has no rank-one element),
  r=10 13 cubes, r=11 3.4M cubes in 2.7 s; x261k cubes per extender
  -> enumeration is hopeless (~1e5 per product). FINDING: the
  structure yields a three-line bound — W's 511 nonzero elements are
  X(x)I_3 with ranks {3:49, 6:294, 9:168}, none of rank <= 2; distinct
  rank-one products inject into the nonzero cosets of W in their span
  (u_i + u_j in W would have rank <= 2), so r <= 2^(r-9) - 1, i.e.
  **rank_F2(<3,3,3>) >= 13** (checker matmul/r22/coset_bound.py;
  F_2-specific coset counting; weaker than Blaser's 19 but instant
  where CDCL needs ~1e9 yr at r=12 and enumeration ~1e11 cubes).
  Dependent coset k-subsets force sums of products to be 0 or rank-3
  elements of W — a finite combinatorial structure for an automated
  substitution-method search (a "rank box"). Conclusion for the
  native-solver design: the inference rules that matter are rank
  subadditivity + coset counting, not parity (PC degree grows with
  r), not permutation symmetry breaking, not enumeration. CDCL
  ladder addendum: r=8 TIMEOUT at 2 h (>= x14 over r=7).
- **Automated substitution method, step 1 PASSED (2026-08-22)**:
  src/bin/subgame.rs plays the kill-one-product game over F_2 exactly
  (state = killed subspaces (U,V,X) as RREF bases, memoized):
  val(T) = max(flattening ranks, max over side and functional phi of
  1 + min over v in the side's SUPPORT with phi.v = 1 of val(T/v)),
  kill only for T != 0. Two lessons from the gate: the plain game
  (adversary kills ANY vector) first returned 12 — a kill-on-zero
  bug the certificate checker could not catch because it encodes the
  same rule (checker != gate: gate on KNOWN values) — then 6, i.e.
  strictly weaker than the literature's substitution method; adding
  the two facts every hand proof uses (a minimal decomposition's
  vectors lie in the side's support, and span it, so the prover may
  force the kill outside any hyperplane not containing the support)
  gives **7 = the exact rank of <2,2,2>**: 132,486 states in 0.55 s,
  373-state certificate replayed from scratch by
  matmul/r22/subgame_verify.py (matmul/r22/subgame_2x2.json). Next:
  step 2 = <3,3,3> as a DECISION procedure ("prove val >= k") with
  alpha-beta pruning and canonical forms under GL_3(F_2)^3 x S_3 —
  gate: reproduce the classical >= 17 (2n^2 - 1); then step 3 = F_2
  refinements (coset injectivity, rank-of-sum, aligned/naive-block
  triples) toward >= 19/20; step 4 = Lean replay of the certificate.
- **Automated substitution method, step 2 in progress (2026-08-23)**:
  subgame gains a DECISION mode (prove val >= k with memoized lower/
  upper bounds, leaf and rank-upper-bound cutoffs, hardest-child-first
  adversary order), canonical forms under the GL_3(F_2)^3 sandwich
  (staged: U over all 28k (P,Q) via action tables, V under the
  stabilizer with R free, X last; phi-orbit reduction under the state
  stabilizer) and certificates that carry an explicit group element per
  merged adversary edge — the checker verifies each element preserves
  the tensor and maps the child onto the canonical node. Measurements:
  plain rules, no symmetry: >= 11 then CAP at k=12 (50M nodes; fan-out
  x256 per level); symmetry: >= 12 in 3,358 nodes but CAP at 13 — the
  prover wandered into the MIXED (U,V) state space (orbits of subspace
  pairs explode); the classical 2n^2-1 = 17 is a ONE-SIDED strategy
  (eight A-kills steering the surviving functional psi to be
  invertible, leaf = the slice psi^T (x) I of rank 9), so --stay
  (prefer the side with the most kills) collapses the search: >= 13
  in 477 nodes / 12 s, >= 14 in 1,629, **>= 15 in 4,118 nodes /
  294 s, 714-state certificate replayed from scratch**
  (matmul/r22/subgame_3x3_stay.json); k=16 capped at 15 min; 2 h run
  pending for 16/17. F_2 coset leaf bound: 13 at the root but the
  adversary breaks its premise with one kill (k=14 CAP at 158k nodes
  with symmetry, 47M without) — a root-only shortcut. Cost is
  canonicalization (~70 ms/state at depth 6); next levers: cheaper
  canonical forms (incremental stabilizers), parallel adversary
  branches, then the F_2 refinements for 18-20.
- **Step 2 GATE PASSED — rank_F2(<3,3,3>) >= 17 by search, and >= 18
  (2026-08-23)**: the {A,B} mixed substitution game with sandwich
  symmetry proves 17 (the classical 2n^2-1) in 556 s sequential /
  375 s with --par 3 (82,747 canonical states); its 57,133-state
  certificate (matmul/r22/subgame_3x3_17.json.gz) replays from
  scratch in matmul/r22/subgame_verify.py. The same run proved
  **>= 18** in 2,576 s (805,565 nodes, 725,899 states; certificate
  too large for the size guard — an uncertified-by-replay search
  result until a compact certificate format exists); k=19 capped at
  1 h. Pre-optimization baseline for the record: the old binary could
  not finish k=16 in 2 h. What made it tractable: (1) A-only is
  exactly 15 (exhaustive, 2.3 s) — the classical proof needs mixed
  kills, like the 2x2 proof (A,B,A); (2) the hidden cost was
  'B-first' mixed states (4.7M-candidate sweeps) — excluded WLOG by
  the S_3 tensor symmetry (--sides AB, root on A); (3) sibling
  orbit-merging under the parent stabilizer (80% of canonical forms
  are merges), L2-resident factored action tables, early rejection:
  ~0.5 ms per one-sided form. Profile of the 1 h run: canonical
  forms 82% (5.7M forms), stabilizers 8%, orbit-merge 5%. State
  growth ~x9 per level -> 19 ~ 9 core-hours, 20 ~ days at the current
  per-form cost; an 8 h --par 4 attempt at 19 is running
  (subgame_3x3_19.out). Whether the plain game's VALUE reaches 19/20
  is the open question (Blaser's 19 used extra arguments).
- **Rank-19 attempt round 1 (2026-08-23, 8 h cap): CAPPED inside
  k=19** — 8.1M nodes, 7.4M proven states, 83.5M canonical forms
  (~102 core-hours): level 19 is >10x level 18 unfinished, worse than
  the x9 extrapolation, and the run spent its last hours under memory
  pressure (31.8 GB RSS, swap 7.3/8 GB — the isos certificate
  bookkeeping). Fixes landed for round 2 (launched at the cap,
  24 h budget): Koszul leaves (--koszul 4; k=17 in 171 s vs 303 s
  parallel-plain, 58,842 states vs 82,531 — real pruning), iso
  bookkeeping skipped without --cert (RSS 1.1 GB vs 31.8 GB),
  5-minute heartbeats. Milestone watcher armed for the k=19 verdict;
  PROVED would match Blaser's 19 by search (certificate re-run
  needed, compact format first); FAILS pins the Koszul+{A,B} game's
  exact value at 18 and makes refinements 2/3 (rank-profile case
  splits, coset/alignment structure) the path to 19/20.
- **Rank-19 round 2 VERDICT (2026-08-24, 01:03): k=19 FAILS — the
  Koszul+{A,B} substitution game has EXACT value 18.** Exhaustive
  refutation, not a cap: 7,482,463 nodes / 4.15 h / 69.3M canonical
  forms, RSS ~2-3 GB (iso-skip fix). Level 19 (koszul) = 6.79M nodes
  ~ 1.1x round 1's unfinished plain prefix. So the search frontier of
  this rule set is exactly 18 — one short of Blaser — and the paths
  up are: (a) --sides ABC (three-sided strategies, the one dimension
  this verdict does not cover; run queued), (b) refinement 2
  (rank-profile case splits) and 3 (coset/alignment structure as
  dynamic rules). ABC verdict (2026-08-24 13:51): CAPPED inside
  k=17 at 12 h / 14.6M nodes / 86M forms — level 17 alone cost 2x the
  whole {A,B} level-19 refutation; the three-sided 18-vs-19 question
  is unanswerable at current per-state cost (needs the round-3
  speedups; deprioritized behind splits). Refinement 2 v1 IMPLEMENTED
  (2026-08-24, --splits):
  per-side min-rank constraints on alive products (state 'u|v|x|r,r,r'),
  split move + kill-coset viability filtering, checker rules from
  scratch; gates passed (2x2 exact 7 with splits; one-sided 3x3 still
  exactly 16; tamper-test negative gate: inflated certificates
  rejected); no gate proof needed a split yet.
  **v1 VERDICT (2026-08-24 19:37): k=19 FAILS with splits too — exact
  value still 18** (7.87M nodes / 5.6 h = the koszul-only refutation
  plus ~50% split overhead; the constraints were explored everywhere
  and bought nothing). Design lesson: using min-rank constraints only
  to FILTER kill cosets is too weak — most cosets contain high-rank
  representatives, so the filter rarely bites. v2 must make the
  constraints strengthen LEAF bounds (rank-profile-aware flattening/
  Koszul/coset arguments) and/or use structured split predicates
  (Blaser cases on subspace shapes, not rank thresholds), and/or
  refinement 3's coset/alignment rules as dynamic moves. The 18-certificate re-run
  VERIFIED (2026-08-24 01:50): 175,932-state certificate
  (subgame_3x3_18.json.gz) replays from scratch — **rank_F2(<3,3,3>)
  >= 18 is now a certified bound**, one short of Blaser.
- **EXTERNAL (found 2026-08-24): rank_F2(<3,3,3>) >= 20 is already
  proven** — Chengu Wang, arXiv:2603.07280 (v1 2026-03-07, v10
  2026-07-30, 'Automated Lower Bounds for Bilinear Complexity over
  Finite Fields'; repo cloned at ~/projects/mmlb-wang, 203 MB with
  certificates + verifier). Method: orbit DP over restriction
  subspaces under (GL x GL) x C2 with four techniques — flattening,
  Hopcroft-Kerr FORCED PRODUCT (extract explicit rank-1 terms,
  enumerate residual coefficients), DEGENERATE REDUCTION (R(T_X) >=
  R(T_Y) for Y within X), substitution with backtracking; 32 MiB
  certificate for >= 20, verifies in ~3 s (their verifier; not
  kernel-checked). Also <2,3,4> >= 19, <3,3,4> >= 25, <3,4,4> >= 29
  over F_2 + 18 polynomial-multiplication bounds. CONSEQUENCES for
  us: the 19/20 target of the substitution-game program is settled
  (our game's exhaustive value 18 stands as OUR engine's ceiling;
  his forced-product + restriction-subspace rules are the leaf
  strengthening v2 was seeking, already worked out); the F_2 open
  band for 3x3 is now 21..23, the rank-22 SAT/certified-tree program
  gains standing; unique niches left for us: independent from-scratch
  re-verification of his certificate, Lean kernel-checked replay
  (his verifier is auditable but unverified), pushing 21 with a
  merged rule set, and the coset/alignment machinery.
  **21-push de-risk (2026-08-24 evening)**: (a) his >= 20 certificate
  REPRODUCED locally (verifier built with bazel: 'OK ... lower bound
  is 20', ~2 s); (b) Koszul-graft experiment NEGATIVE and decisive
  (matmul/r22/koszul_vs_wang.py): our Koszul bound beats his recorded
  orbit bounds on 1 of 496 orbits (dim-6 index 70: 13 -> 14), and at
  the load-bearing dims 0-4 sits at 14-15 vs his backtracking's
  17-20 — his recursive backtracking dominates all our leaf bounds.
  Revised 21 levers: (i) budget probe — rerun his DP at dims 0-2 with
  enlarged backtracking_step_limit / forced_product iterations to
  learn whether 21-at-root is budget-limited; (ii) symmetry probe —
  whether his backtracking exploits B/C-side symmetry (our sandwich
  machinery) inside the recursion; (iii) new techniques (coset/
  alignment; multi-mode forced product).
  **Probe results (2026-08-24 23:00)**: (ii) READ — his backtracking
  is A-side-only substitution chains (rank >= |S| + orbit bound);
  NO technique constrains B/C (forced product only cyclic-transposes
  at leaves) — with our measured A-only=16 vs mixed=18, B-side
  substitution inside the recursion is the leading fifth-technique
  candidate. (i) POSITIVE at dim 2: 200x budget OOM-killed at 72 min
  (his caches; watchdog added), but 30x budget with 2M-entry caches
  lifted EVERY dim-2 orbit: shipped {17x1,18x13} -> {18x12,19x2} in
  ~55 min — the near-root layer is BUDGET-LIMITED, not fundamental.
  Cascade dims 1-0 on the enriched dim-2 layer alone: root UNCHANGED
  at 20 (dim-1 stays 19; with only 2/14 dim-2 orbits at 19 the root
  arithmetic 1+19 cannot exceed 20) — as expected, the lift must be a
  wave from the deep layers (shipped maxima: dim-4 17, dim-3 18).
  FULL-depth cascade VERDICT (2026-08-25 15:13, 16.1 h; certificate
  VERIFIED by his verifier after repairing my output_path mistake —
  a fresh --output_path starts an EMPTY .btp archive, orphaning the
  shipped traces of unimproved orbits; merged per-orbit, 20 new
  traces + 238 shipped, matmul/r22 merge note): the wave lifted the
  WHOLE lattice — dim 4 max 17 x73, dim 3 {17x23, 18x41}, dim 2
  {18x6, 19x8} (shipped {17x1, 18x13}), dim 1 all 19 — but the ROOT
  HELD AT 20. A 21 root needs dim-1 at 20 needs all 14 dim-2
  branches at 19 (8/14 are). Returns per budget multiple are
  decaying near the root (30x: dim-2 all +1 initially, full wave
  8/14 to 19, root +0). Reading: not provably fundamental, but
  budget-only scaling is in diminishing returns — the fork is
  ~10-30x more budget (days; REQUIRES the memory fixes: inline map
  keys, malloc_zone_pressure_relief between orbits, byte-budgeted
  caches, per-dim process runs — footprint hit 100 GB from allocator
  retention) vs the fifth technique (B-side substitution inside his
  DFS with our sandwich canonicalization; his framework is A-side
  only and our measurements show mixed-side is strictly stronger).
- **B-side substitution implemented in Wang's DFS (2026-08-25,
  trlb-wang branch bside-memfix, commits b576508 memfix + 06b1225
  b_side)**: the fifth technique — when a node's A-children all fail,
  roll the trace back and extend on B (all leading-One covectors);
  pure-A subsets still bound via the orbit map, mixed subsets via the
  flattening rank of the doubly-restricted tensor (j-axis mirror of
  ApplyConstraintsToTensor). Proof body v2: per-record leaf_kind +
  pre-order side-bit stream for internal nodes, EOF-probed for
  backward compat; A-only runs stay byte-compatible (side slots only
  reserved under --b_side — an unconditional slot polluted archives
  and broke asym verification until guarded). Verifier replays
  recorded side choices and recomputes mixed leaves from scratch.
  Gates green: n222 --b_side root 7 (known exact), n223 asym root 11
  (Hopcroft–Kerr exact) + clean --b_side refusal (kNB != kNA), both
  n333 certs (shipped + 30x-cascade) verify at 20 under new binaries.
  M-gate: memfix binary reproduces the 30x probe bounds {18x12,19x2}
  exactly (memory trace inconclusive — sampler tracked wrong PID; RSS
  now sampled inside the arms run instead). NOTE: no mixed record has
  yet passed the verifier — tiny problems never fail on A, and 100M
  steps can't lift cascade dim-2 (at {18x6, 19x8}), so the mixed
  replay's first real exercise is the production experiment. Launched
  2026-08-25 ~22:00: two-arm equal-budget dim-2 at 3B steps/orbit
  (arm A: A-only control; arm B: --b_side), same input copies of the
  cascade cert, bound histograms + verification + B-usage dump at
  the end (probe/dim2_arms.{sh,log} in trlb-wang).
- **Two-arm equal-budget dim-2 verdict + mixed-leaf soundness fork
  (2026-08-26, trlb-wang fb16252)**: the 3B-step arms were infeasible
  (all 14 orbits burn full budget at depth; deep harvest cost => >3 h
  for orbit 1; also the first launch dragged the 976 MB trace archive
  resident (~30 GB) into swap — archive is save-time-only, stripped
  thereafter). At 300M steps: arm A (A-only) {18x6,19x8} -> unchanged;
  arm B (--b_side, B-after-full-A-failure) also unchanged — but
  instrumentation proved arm B VACUOUS: A 'fails' by budget
  exhaustion, then B runs against the dead counter (B tried, 0 mixed
  leaf evals). Fixed by alternating per-node side priority (odd
  depths B-first; sound wrt the proof contract — only the winning
  side is recorded). The instrumented 10M rerun then exposed the real
  fork: 48k B-attempts, 99.99% rescue rate, 43.5M mixed-leaf evals —
  implausible; the mixed-leaf rule (popcount + flatten of the
  doubly-restricted tensor) assumes every chain constraint stays
  active, which pure-A chains get free (A-flattening injectivity)
  but mixed restrictions violate (A columns vs B rows can annihilate
  products) — each inactive constraint inflates +1. No false lift
  escaped (adversary-min held roots; histograms flat) and the n222
  root-7 gate does not certify the rule (checker is not a gate).
  OPTIONS: (a) activity guards at mixed leaves — require full
  marginals of the doubly-restricted tensor (two rank checks per
  eval), then rerun the arms; (b) graft subgame support/spanning
  discipline; (c) B-side orbit-map canonicalization (the original
  'sandwich' plan) replacing flatten leaves. --b_side stays
  experimental; no bound from it is to be believed yet.
- **Equal-budget dim-2 arms, guarded rerun — REAL NULL (2026-08-26,
  trlb-wang d7c9cee)**: activity guard implemented, validated (python
  formula check on engineered deactivations; C++ probe — initial FAIL
  was the probe writing GFVec elements via operator[], a silent no-op
  on the bit-packed type; known-value gates 7/11 green), and BINDING
  in production: per-orbit deficit_total ranged 0 .. 8.6B docked
  credits (transpose-dual orbit pairs show mirrored search counts
  with opposite-side activity). Arm A (A-only, 300M steps):
  {18x6,19x8} unchanged, ~1 h. Arm B (--b_side, alternating,
  guarded, 300M steps): {18x6,19x8} unchanged, 8.5 h, ~100B sound
  mixed-leaf evals total, B-rescue rates 92-99.99% at internal
  nodes, 0 surviving traces. The treatment provably ran (millions of
  rescues); no orbit's root fanout closed within budget — mixed
  steps cost ~40-80x more evals per step, and the B fanout has NO
  coset reduction (no base on B) and NO iso-dedup of mixed subsets,
  so the ~100B evals are largely isomorphic repeats. DIAGNOSIS: raw
  mixed search is eval-starved by redundancy, exactly what A-side
  orbit canonicalization cured in Wang's DP. Fork: (c) B-side/mixed
  orbit-map canonicalization (the original sandwich plan) is the
  remaining lever inside his framework; alternatively fold the
  residual-rank + GE + dynamic sandwich-symmetry stack into a
  CDCL(T)/SMS-style propagator architecture (discussion recorded
  2026-08-26) and pursue the certified-search route. --b_side +
  guard stay sound and committed; no bound changed.
- **(c) Wang-table graft + dim-2 mixed-play campaign — 14/14 CAP
  (2026-08-27, logic 46dd1ea)**: subgame gained --wang-table (his 496
  verified A-side orbit bounds, exported from the cascade cert, keyed
  by OUR canonical forms, both tau-variants) as a sound pure-A leaf,
  and --root-u ladders from any A-restricted state. Gates: full root
  k=20 and dim-2 root k=18 prove in 1 node. Campaign: all 14 dim-2
  orbits at k=table+1 (--sides AB --sym --par 4, 1 h/orbit): every
  orbit CAP at 500-850K nodes, ~200 states/s, canon-cache >90% hits,
  adversary refuting 97-99.99% of explored states; koszul-4 arm on
  orbit 0 (2 h): identical texture, null. Third independent null
  (after C++ arm B and the guarded rerun): budget, symmetry,
  soundness, and koszul are all eliminated — the binding constraint
  is MIXED-LEAF STRENGTH (flattening-class ~14-16 once play leaves
  the pure-A lattice). Fleet math for a k=21 push (Greg's question):
  ~50-400 machine-days on 512-core/TB nodes IF the answers are
  PROVED — but linear frontier growth at 2x budget and the refutation
  rates lean FAILS, and one FAILS among the six 18s kills the route.
  CALIBRATION launched on campaign completion: 8 dim-4 + 6 dim-3
  orbits at table+1 (45 min / 2 h caps) to fit exhaustion node-counts
  vs quotient dim and decide PROVED-vs-FAILS cheaply
  (matmul/r22/calibration.sh).
- **Exhaustion calibration + CDCL(T) stage-1 (2026-08-28, logic
  ede3f87/79e4393)**: dim-4 sample (8 orbits, table+1): 7 FAILS
  exhausted at 137-391K nodes (16-40 min each), 1 CAP >492K; dim-3
  sample (6): 1 FAILS at 206K (the hyper-symmetric u=1,2,4 root —
  big stabilizer collapses the space), 5 CAP at 1.10-1.34M after 2 h.
  Fit: exhaustion grows >=5-10x per lattice level; generic dim-2
  verdicts ~10^7-10^8+ nodes = 16-160+ h/orbit on the M-series Mac;
  dim-1/root multiply again (fleet scale). Decisive datum: ALL EIGHT
  exhaustive verdicts are FAILS — no PROVED anywhere in the sample;
  the mixed game with flattening-class leaves provably cannot lift
  table+1 down-lattice, so fleet compute would buy confirmations of
  impossibility, not lifts. ABC campaign (C-side move set, route 1)
  auto-launched at calibration close. CDCL(T) stage-1 (route 2,
  src/bin/schemesearch.rs): product-level search + residual-rank
  propagators reproduces BOTH certified 2x2 values — r=6 UNSAT
  exhausted (3.22B nodes/192 s structural prunes; 4.3M/6.7 s with the
  sound full-lambda 1-ply substitution probe = 746x tree cut, the
  architecture thesis quantified) and r=7 SAT with an independently
  verified witness. Two unsound cuts (alpha-canonical first product;
  lambda=0-only probe) produced a false r=7 UNSAT and were caught by
  known-value gates — proof logging is mandatory before any novel
  UNSAT claim. Next: SMS set-prefix canon, proof logging, 3x3 lazy
  product enumeration with Wang-cert gates at every rank <= 19.
- **Route 1 (C-side move set) CLOSED — inflation without power
  (2026-08-28)**: ABC campaign, all 14 dim-2 orbits at table+1, same
  protocol as AB: 14/14 CAP. Texture: 1.2-5.9M nodes/orbit (2-8x the
  AB counts) but refutation saturation COLLAPSED from ~98% (AB) to
  5-13% (ABC) — the three-sided fanout sprawls through a vastly
  larger, mostly unresolved space (canon revisit rates way down =
  virgin territory, not contest). Discriminators on dim-4 states
  where AB FAILS exhaustively in 16-40 min (par 4): four ABC par-1
  runs all CAP at 90 min; the equal-parallelism rerun of d4_0 (AB:
  FAILS 186K nodes/25 min) CAPs at 4 h / 1.23M nodes — >=6.6x node
  inflation, verdict unreached, and NO PROVED appeared anywhere in
  18 ABC runs on spaces where a real lift should be easy to exhibit.
  Verdict: C-moves inflate the game without observed proving power;
  consistent with (and further evidence for) the mixed-leaf-strength
  diagnosis. Remaining levers: route 4 (mixed-orbit DP with his
  P2/P3 techniques on doubly-restricted tensors), route 2 (CDCL(T)
  stage 2+: SMS canon, proof logging, 3x3 lazy products), route 3
  (upper-bound hunt at rank 22 via flip/LLM-evolution), write-up.
- **CDCL(T) stage 2 — 3x3 ladder measured; reach = rank > 10
  (2026-08-29, schemesearch3)**: lazy 511^3 product space (no
  materialized list), 729-bit residuals, sound alpha-rep WLOG
  (over-counting form), 12-thread parallel top level (deterministic
  node totals; ~10x wall). Ladder: r=9 UNSAT 783K nodes/0.1 s
  (flatten alone) => rank > 9; r=10 plain CAP 437M/10 min but probe
  UNSAT at the SAME 783K frontier in 23.6 s => rank > 10 — one ply
  of substitution reasoning moves the ceiling exactly one rung at
  ~0.36 ms/probe (256-fold lambda range); r=11 plain CAP 3.44B
  (5.7M nodes/s), r=11/12/13 probe CAP at 113M/227M/485M over
  1/2/4 h — the 1-ply bound saturates at 10, so its prunes start at
  depth 2 and the fanout wins. STAGE-3 REQUIREMENTS (data-fixed):
  (i) Koszul-strength propagator on residuals (general-tensor, up
  to ~14-16, port koszul_side; depth-gated), (ii) second-level
  stabilizer symmetry (enumerate product 2 modulo stab of the
  alpha-rep residual; fanout_orbits says 10-100x), (iii) on-demand
  2-ply probes at frontier nodes only, (iv) proof logging BEFORE
  any r >= 20 rung (stage-1 lesson: two unsound cuts already died
  on known-value gates), (v) flatten kernel optimization (~10x:
  extract81 loop -> precomputed transposes; probes are
  flatten-bound). Output phrasing now 'rank > r' (Greg 2026-08-28).
- **CDCL(T) stages 3-4 complete — rank > 14 in 0.1 s; the routes
  converge (2026-08-29, logic 88d88fb/501f33d/03d9d52)**: stage 3
  (triple-layout kernels; 211 first-product orbit reps of 133.4M —
  632384x; Koszul propagator) took rungs 11-14 at 211 nodes / 0.1 s
  each — level-1 Koszul is uniformly 14 across all 211 root
  residuals. Stage 4a (level-2 stabilizer minimality, median 16x):
  sound, regressions green, r=15 still CAP at 456M nodes/2 h. Stage
  4b (learned rank certificates): minor extraction + restricted-
  generator transfer implemented; the design's risk gates fired —
  transfer decay is EXACTLY 1 per product (300/300; perturbation
  generators always full-rank in the minor), koszul rises on random
  paths (alignment is rare, no filter variance), and the per-p curve
  on level-2 residuals (11/12/13.5/14 at 0.27/1.2/3.3/6.1 ms) means
  only p=4 prunes r=15's level 2 — pricing that rung at ~100
  Mac-days (~2.5 days on a 512-core node) and rungs >= 16 above
  Koszul's ceiling entirely. VERDICT: route 2's architecture thesis
  is proven (structure-aware inference: 6 rungs in 0.1 s where plain
  search capped at 10, each propagator worth its exact theoretical
  strength), and its bound-strength converges with route (c) on the
  identical missing object: a cheap strength-15..19 rank oracle for
  arbitrary (not lattice-restricted) tensors. The week's three
  independent programs — Wang-DP mixed play, the exhaustive game,
  and certified scheme search — all terminate at that one gap.
- **Tier-2 ply ladder + kernel work + corridor verdict (2026-08-30/31,
  logic da94bce/841a13b)**: TIER 2 REFRAMED — the sound "for all
  children" quantifier IS a game ply, so tier 2 = substitution probe
  with KOSZUL leaves. Ply-1: exactly 14 on all 211 roots (adversary
  always owns a koszul-dropping fold). Ply-2 (33 min, 12 threads):
  {14: 72, 15: 139} — two thirds of the roots refute their whole
  r=15 subtree at level 1, leaving a 72-root hard core. Ply-3
  untimed was measured INTRACTABLE (16h44m at 1190% CPU, <8 of 211
  roots); relaunched time-boxed (--root-budget, expired budget =
  'unresolved', never a value: an incomplete min over adversary
  folds is not a sound bound). KERNELS: M4R forward-only rank
  implemented and equality-gated, then benched OUT of the koszul
  path (1.26x dense but 1.5x SLOWER on the sparse wedge shape —
  legacy short-circuits on sparsity; dense-benchmark extrapolation
  was the error); wedge index tables cached; rank9 rewritten to
  leading-bit reduction (O(9^2) instead of an 81-column scan) =
  2.10x gate-verified on 200K cases, universal since rank9 sits
  under every flatten/probe/ply. NEON intrinsics deliberately not
  used: the cost was iteration count, not lane width. CORRIDOR
  (rank-22 arm) FAILS GEOMETRICALLY: prefix descent has no guidance
  signal — flatten is capped at 9 (constant while remaining >= 9)
  and popcount descent is stuck at the start because T has 27 of 729
  bits set while a random rank-one sets ~91 (greedy: depth 1, 30
  restarts; v2 flatten-guided: depth 9, 0 near-misses at the
  known-SAT target 23). True-scheme intermediates are low-RANK, not
  low-popcount. Correct pipeline instead: src/bin/anf.rs (native-ANF
  Brent SLS mod 2, --emit-best) supplies near-misses -> drop k
  products -> schemesearch3 --endgame completes or refutes exactly
  (endgame engine built, refutes junk prefixes in ms). best_gamma
  (greedy-optimal gamma for fixed alpha,beta) is retained: it is the
  exact inner step for the SLS bridge.
- **INDEPENDENT rank > 15 — killer-directed deep probe takes the rung
  (2026-08-31, logic 656876a + this commit)**: ply-3 fixed sweeps
  died (16h44m untimed: <8/211 roots; 15-min boxes: 72/72 core roots
  unresolved — {15(ply2):139, unresolved:72} final). Item 1 replaced
  them: deep_probe = lazy substitution recursion, cheap-floor chain
  (flatten -> strassen -> koszul) at every node, recursion only into
  KILLER folds (koszul-droppers); targets fall into strassen range
  within ~2 levels so depth self-limits. Measurement: all 211 roots
  prove >= 15 in 3.2 h/12 threads (fixed ply-3 couldn't touch one in
  16 h). Official ladder: r=15 UNSAT — exhausted at 211 nodes,
  3.25 h => rank_F2(<3,3,3>) > 15 with the engine's own machinery
  (no Wang citation). deep_probe_par added (fanned 2^8-fold sweep,
  conjunction w/ early abort) for one-root x huge-probe shapes; the
  t=16 reach test runs on it next (~46 core-h/root naive estimate;
  killer early-exits may beat it). Perspective kept honest: r <= 19
  rungs are trivial via subadditivity + Wang (20 - k floor);
  independent rungs measure ENGINE strength, and novelty still
  starts at r=20 where every bound is structurally +1 short.
- **t=16 reach test verdict — out of reach; ladder rests at rank > 15
  (2026-08-31 21:31)**: root 0 alone consumed >= 70 core-hours
  without resolving (killed for a system update; vs 0.65 core-h/root
  at t=15). Scaling: the r=16 rung >= 1.5 core-years on this Mac.
  The recurring law: each technique buys its theoretical strength
  then walls one rung later at ~100x. Independent-engine resting
  point: rank > 15 (602baf7). Post-update agenda: r=20 mathematics
  (killer-variety characterization from the banked fold data,
  decomposition-structure theorems), and the write-up.
- **THE RANK LAW of killer folds (2026-08-31, killer-dump)**: dumped
  all koszul-dropping folds at the 211 roots (10,338 killers, 90 s).
  Every killer drops 14 -> exactly 13; pivot always cell (2,2). LAW:
  with the folding covector phi = e_(2,2)+lambda viewed as a 3x3 F2
  matrix — rank(phi)=1 => killer (633/633 pairs, no exceptions;
  the 16 rectangle indicators through the pivot = the observed 16
  killers/pair); rank(phi)=3 => non-killer (no exceptions);
  rank(phi)=2 => killer only at 38 exceptional pairs on 30 roots
  (210 extras; reps skew low-rank-factored, but two (2,2,2) cases
  say factor ranks alone don't decide the boundary). READING: the
  adversary's dangerous moves are PRODUCT-SHAPED (rank-1, aligned
  with the tensor's rank-one structure) — same objects as the
  subgame's rank-profile splits. CONJECTURE (case-split lemma):
  rank-3 folds preserve koszul >= 14; proven, ~168/256 probe evals
  vanish (rank-2 boundary too: 240/256), repricing t=16 from
  >= 1.5 core-years to days. Files: matmul/r22/killers.txt,
  killer_analysis.py. Write-up in progress.
- **The killer mechanism, fully quantified (2026-09-01,
  --hyperplane-koszul + --wedge-correlate)**: base values by finite
  verification — koszul(T|ker phi) depends only on rank(phi) (all
  511 covectors x 3 sides): 13/14/14 for ranks 1/2/3; class
  constancy exact, so the sandwich-orbit invariance is now a
  theorem-by-exhaustion. Subadditivity alone does NOT give the
  case-split lemma (k3 = 14, not 15). The correlate (8 roots x 256
  folds; side-A p=4 wedge): perturbation wedge b = 70 always;
  v_T = 918 (rank-2/3) / 900 (rank-1); wedge drops are QUANTIZED to
  {0, 6, 12} — the 8..11 band killerhood must cross is empty.
  Killer <=> two 6-units of drop; rank-2 aligned cases hit 12
  exactly (v_R = 906); rank-3 never exceeds one unit; rank-1 kills
  by inheritance (base 900 <= 910, drop irrelevant). Intersection
  dims step in 3s (35/38/41). LEMMA, proof-shaped: for rank-3
  covectors the perturbation achieves at most one 6-unit of drop —
  WLOG phi = identity (orbit transitivity measured), decompose the
  wedge under Stab(phi), bound the aligned piece. The 6- and
  3-quantization points at small isotypic components.
- **CASE-SPLIT LEMMA PROVED by orbit exhaustion; sandwich-action bug
  found and fixed; 52/211 roots were never probed (2026-09-01,
  --fold-lemma / --orbit-audit)**: THEOREM: for every rank-one m
  (all 511^3) and every fold vector v of matrix rank 3, on any side,
  koszul(p<=4) of (T+m)|ker v is exactly 14 — the side-A p=4 embedded
  wedge never drops below 912 (threshold 911); rank-3 folds never
  kill. Proof = finite verification: sandwich transitivity puts v at
  the class rep I; the 7,029 orbits of m under Stab(I) x GL3(R) are
  enumerated by a staged lex-min canonical form whose orbit sizes sum
  to exactly 511^3 (completeness gate); every orbit evaluated (5 s).
  Drops: 0 on 6,505 orbits (122,193,407 products), exactly 6 on 524
  (11,239,424) — each 6-unit is 3+3 across the two HONEST 8-dim
  wedges (p=3 and p=4 on A/v, both of rank 459; the embedded p=4 rank
  918 = h3 + h4, asserted throughout). Rank-2 class (v = E22+E33,
  14,070 orbits): drop 0 / 6 / 12 on 12,898 / 1,064 / 108 orbits;
  the 108 killer orbits (774,144 products, 0.58%) drop exactly 6+6 to
  koszul 13 — the rank-2 boundary is now a finite TABLE (Stab(v)-orbit
  lookup), not a search. Rank-1 class (3,556 orbits): base 900, every
  product is a killer by inheritance; drops -6/0/6/12/22 (rank can
  RISE by 6; the 22 = 10+12 asymmetric cases break the 6-quantization
  where it no longer matters). Necessary conditions for the rank-2
  killers (all 108): tr(alpha beta gamma) = 1, tr(v beta gamma) = 0,
  rank(alpha) <= 2, alpha != v; no combination of <=3 matrix-rank/
  trace invariants is a pure classifier, so the structural (isotypic)
  proof stays open — the exhaustion IS the proof. GATES: T-invariance
  of the action on 20 random elements; 40 random (m, v) transports;
  transport of every (root, side, lambda) probe fold to its orbit rep
  — 162,048 triples on the corrected roots and again on the pre-fix
  roots, 0 mismatches; the predicted killer set of the pre-fix roots
  is BYTE-IDENTICAL to killers.txt (10,338 lines). Files:
  matmul/r22/fold_lemma_rank{1,2,3}.txt (orbit tables), fold_lemma*.out.
  BUG (caught by gate 1): first_product_reps ported subgame.rs's
  C-side action gamma -> P^-1 gamma R^-1 verbatim, but subgame indexes
  C as (i,k) and schemesearch3 as (k,i); in the (k,i) layout the
  action is R^-T gamma P^-T (transpose). The ported action is NOT a
  symmetry of T, so the 211 "orbit reps" were reps of a fake orbit
  partition: --orbit-audit shows they hit only 159 of the 211 TRUE
  first-product orbits (52 never probed; alpha/beta stages were
  correct, only gamma minimization was off). Fixed in act_gamma (one
  site; stabilizer elements — hence the level-2 4a pruning — are now
  true stabilizers). Repairs: r=14 rung re-exhausted on the corrected
  211 roots (0.7 s, koszul 211/211); r=15 deep probe re-run on the 52
  uncovered orbits (matmul/r22/uncovered_roots.txt, r15_uncovered.*)
  — see the next bullet for the verdict. Every root-set statistic
  before this date (killer dump, ply-2 histogram, t=16 root-0 cost)
  was measured on the 159-orbit subset plus 52 fake reps; the Rank
  Law and the killer mechanism are unaffected (the lemma quantifies
  over ALL products). NEXT: the t=16 reprice needs the LEVEL-2
  statement — (T+m)|ker<v,v'> for 2-dim fold subspaces; same
  machinery (pencil classes of <v,v'> x Stab-orbits of m), larger
  but finite.
- **r=15 rung REPAIRED on the 52 uncovered orbits; work-queue probe
  for full 12-core use (2026-09-01 evening)**: deep probe t=15,
  depth 6 on the 52 true first-product orbits the pre-fix roots never
  hit: 52/52 prove rank >= 15 (394 s wall, --probe-par, 0 failures;
  matmul/r22/r15_uncovered.err). With the 159 orbits the old roots did
  cover (their proofs transfer orbit-wise), the independent ladder
  rank_F2(<3,3,3>) > 15 now rests on a COMPLETE, gate-verified set of
  211 true orbit reps; r=14 re-exhausted the same way (0.7 s). Core
  utilization (Greg: always use the 12 performance cores): the
  root-parallel mode tails to one busy core (1 hard root of 52 ran
  ~4 min alone at 100%); --probe-par fans only the top level and sat
  at ~8 cores (each hard fold's recursion is serial inside its
  worker). New deep_probe_pool (--probe-pool): one global task queue
  over the whole AND-OR tree (sides sequential, so the serial tree's
  work; every fold at every depth is a task; early abort by ancestor
  flags) — truth value gated against the serial probe on six cheap
  recursion cases and against the recorded fanned verdicts on three
  deep t=15 roots (--probe-pool-test): all agree; sustained 1090-1100%
  CPU with 12/12 workers busy (matmul/r22/pool_gate.log; 1,10,64 in
  12.9 s over 65,792 tasks). Use --probe-pool for hard roots and any
  t=16 attempt.
- **LEVEL-2 FOLD LEMMA by orbit exhaustion + the no-op-fold finding
  (2026-09-01 night, --fold-lemma2)**: two side-A folds = quotient by a
  2-dim subspace U of A. Classes: 17 GL3xGL3-orbits of the 43,435
  2-dim subspaces (pencil types; orbit sizes sum exactly). BASE
  koszul(T|ker U): 12 or 13 for the 9 classes whose pencil contains a
  rank-1 matrix or is the (2,2,2) pencil with |Stab| = 288 (class 8);
  exactly 14 with e4 = 918 (the level-1 value!) for the 8 classes of
  rank profile (2,2,2)/(2,2,3)/(2,3,3)/(3,3,3) without a rank-1
  member. Then every Stab(U)xGL3-orbit of m evaluated (1.65M orbits,
  25 min on 12 cores; sizes sum to 511^3 per class; transport gate
  300/300): classes 0-8 have ZERO leaves for any m (rank can rise by
  up to 12 and never reaches 911) — the Rank Law one level down: a
  rank-1 vector anywhere in the fold subspace kills; classes 9-16
  keep koszul 14 on 96.65-99.90% of products (killers drop exactly
  12 or 18 = 6-units again). Over ALL (U, m) pairs the level-2 leaf
  fraction is 71.92%. Tables: matmul/r22/fold_lemma2_tables.tgz
  (per-class orbit tables), fold_lemma2.out. NO-OP FOLDS: after a
  fold the pivot coordinate is a zero slice, but deep_probe's lambda
  still ranged over all 8 other coordinates; a fold INTO a zero slice
  is an isomorphic relabeling, not a quotient (a minimal decomposition
  projects off any zero slice, so alpha vanishes there). Half of the
  level-2 folds, 3/4 of level-3, 7/8 of level-4 were wasted evals.
  Fixed in deep_probe / deep_probe_par / the pool (lambda over ACTIVE
  coordinates only; sound; cheap gate + recorded-verdict gate agree).
  t=16 reach test relaunched on root 0 with the pooled probe + fix
  (30-min cap) — verdict in the next bullet.
- **t=16 root 0 still out of reach at 6 core-h (2026-09-01 late)**:
  pooled probe + active-coordinate folds, depth 8, 12 cores, 30-min
  cap: unresolved (exit 124; t16_root0_pool.err). Better than the
  70-core-h no-verdict of 2026-08-31 in cost, not in outcome. NEXT
  LEVER: fold-orbit pruning under the residual's stabilizer — root 0
  = (E11,E11,E11) has |Stab| = 768, so its 256 level-1 folds collapse
  to a handful of orbits (sound: rank(R|ker gv) = rank(R|ker v) for g
  in Stab(R), so one rep per orbit proves the whole AND); recurse
  with Stab(m, v). Plus per-depth task/leaf statistics from the pool
  to see where the tree actually spends.
- **t=16 verdict with every lever applied: still a wall; the profile
  says why (2026-09-01/02 night)**: pooled probe + active-coordinate
  folds + FOLD-ORBIT PRUNING under Stab(root) (root 0 = (E11,E11,E11),
  |Stab| = 216: level-1 fan 256 -> 28 reps, level-2 1536 -> 1440;
  sound, gated: verdicts equal the serial probe on 6 recursion cases
  and the recorded t=15 verdicts on 4 roots; t=15 on root 1,10,64
  went 65,792 -> 6,144 -> 1,473 tasks through the three levers) —
  30-min cap, 12 cores: UNRESOLVED (exit 124). Per-depth profile at
  1740 s (t16_root0_sym.err): depths 0-3 run 0/12/12/24 nodes, depth 4
  1,331, depth 5 82K, depth 6 266K, depth 7 991K, depth 8 3.36M with
  427,697 failures AT THE DEPTH CAP (target 8 on a 1-slice residual
  needs flatten >= 8) — i.e. in 29 min the search had not finished
  ONE level-2 subtree; the cost is intrinsic to targets 11..8 at
  depths 5..8, where the floors (flatten <= 9, koszul ~10-11 on 3-4
  A-slices) sit below the target. BALANCED side order (fold the side
  with most active coords) tested as --balanced: verdict-equivalent,
  but LOSES at t=15 (root 84,10,142: 0.44 s -> 126 s; 1,10,64: 0.39 s
  -> 11.8 s) because keeping all sides near 9 active keeps every
  level's fan at 256 while A-first halves it per level; not the
  lever. STANDING VERDICT: rank > 15 is where substitution+Koszul
  rests; t=16 needs a stronger intermediate oracle (rank >= 11..13 on
  3-4-slice residuals), not more search engineering. Machinery kept:
  --probe-pool (12-core work queue, per-depth stats every 60 s,
  --no-fold-sym, --balanced), --fold-lemma / --fold-lemma2 tables.
- **Subspace MEMO TABLE in the pooled probe; SAT oracle ruled out;
  pencil formula over F2 is NOT n+m (2026-09-02)**: the residual after
  any fold chain is the projection of the root along U = span(folds)
  onto the non-pivot coordinates, a function of U alone, so the
  reduced-echelon bases of (U_A, U_B, U_C) are an EXACT key (same
  embedded tensor, same target, same depth budget). Implemented as a
  sharded transposition table (--no-memo to disable); genuine OR/leaf
  verdicts only (stale-skipped children never report, so orphans are
  never stored). Gates: serial equality on 6 cases, recorded verdicts
  on 4 t=15 roots. Root 1,1,1 at t=15: 42.8 s -> 13.3 s (96K -> 30K
  tasks). t=16 root 0, 30-min cap: STILL UNRESOLVED; 3.83M memo
  entries, hit rates 15-50% by depth (t16_root0_memo.err). Why the
  pure-A redundancy (2^10 at depth 5, 2^28 at depth 8) does not
  materialize: pure-A chains bottom out at depth 7-8 (pencils whose
  three combinations all have rank <= 7), the probe then folds side B
  or C, and the mixed keys (7 A-folds + 1 B-fold: 2^14 x 256) are
  millions — the deep layers are side-switch fan-outs, not
  revisits. Profile at 1740 s: depth 7 847K run, depth 8 2.83M run
  (181K genuine failures at target 8). SAT AS ORACLE (cadical, naive
  Tseitin of the k x 9 x 9 rank-<=r system, matmul/r22/tensor_sat.py):
  DEAD — a 9x9 pencil of known rank 9 (3 x L_2) needs 3.5 s for the
  SAT side and >60 s for rank<=8 UNSAT; random pencils time out at
  every r in 8..11. PENCIL FORMULA: brute-force min_X [rank X +
  rank(I+X) + rank(A+X)] on regular pencils (I, A), n<=4
  (matmul/r22/pencil_check.py): the classical n + #(non-squarefree-
  split invariant factors) is WRONG over F2 — an irreducible cubic
  block contributes +2, (x+1)^4 contributes +2, an irreducible quartic
  +2; block additivity held in every sample. An exact pencil oracle
  therefore needs Kronecker form over F2 + a per-block rank table
  (blocks up to size 9, computable by brute force/SAT once) + a
  verified additivity gate. Expected value: removes the depth-8 layer
  (~70% of t=16 work) and settles depth-7 pencils exactly — roughly
  3x, which does NOT reach t=16 on its own; the wall is depths 5-6
  (3-4-slice residuals at targets 10-11) where no cheap exact oracle
  is in sight.
- **The depth-5/6 failures, dissected (2026-09-02, --dump-hard +
  hard_residual_analysis.py + compressed_sat.py)**: 4,498 residuals
  dumped from a 3-min t=16 run on root 0 (thinnest side with 3-4
  active slices; "hard" = every floor fails, "leaf" = Koszul settles;
  any side mix). STRUCTURE: hard and leaf residuals look the SAME —
  common kernel of dimension 3 (occasionally 4-5), row span 6, column
  span 6, slice ranks 2-3 (3-slice) or 1-4 (4-slice) — i.e. they are
  CONCISE 3x6x6 / 4x6x6 / 3x6x5 tensors embedded in 9x9 coordinates;
  the only difference is Koszul 8 (leaf) vs 7 (hard) at target 8.
  The pure-side-A hard nodes (14 of 4,498) are the degenerate ones
  (slice ranks 2,3,3 -> rank <= 8 < 10): an upper-bound early-fail
  (sum of ranks of a greedy low-rank basis of the slice span, sound
  and verdict-preserving, --no-ub-fail to disable) catches exactly
  those and fires only ~2,300 times in 29 min — the bulk is NOT
  refutable that way. EXACT RANK by SAT on the compressed instances
  (98-140 variables): rank <= target is SAT in 0.0 s on every sample
  (so true rank <= target), rank <= target-1 times out at 120 s on
  every sample: the hard nodes are (almost certainly) TRUE nodes of
  rank exactly the target that Koszul misses by one and nothing cheap
  certifies. ORACLE VERDICT: no lower-bound oracle is in sight for
  concise 3-4 x 6 x 6 tensors at ranks 7-9 over F2 (SAT UNSAT-side is
  minutes+, no closed form). What IS in sight, and is the real
  diagnosis of the wall: the probe folds in the 9x9 coordinates, so a
  concise 3x6x5 residual still fans 2^8 on sides B and C where a
  basis of the 6-dim slice span would fan 2^5; and the depth cap 8
  cuts exactly where those small subtrees (fans 4/32/16/8...) would
  finish the proof by flatten. RECOMMENDATION if the t=16 push is
  reopened: (1) reduce every residual to its concise form (rref the
  slice matrices on all three sides; an isomorphism, so sound), (2)
  key the memo by the concise tensor + (target, depth) instead of the
  fold subspaces, (3) raise the depth cap to ~12, (4) gate with
  known-value tensors (<2,2,2>: true at 7, must be false at 8).
  Expected effect: the deep layers' fans drop by 8-16x per level and
  the cap failures (181K/run) disappear; whether the level 1-4 tree
  (about 3,000 depth-3 nodes x their subtrees) then fits a day is the
  measurement to make. t=16 remains unresolved at 30 min x 12 cores in
  all three configurations tried today (memo, ub-fail naive, greedy).
- **CONCISION changes the game (2026-09-02 morning, cf0f089)**: every
  residual is rewritten in bases of its slice spans on all three sides
  (rref of the 9 slices per layout = change of basis on that factor,
  an isomorphism); the memo is keyed by the concise tensor + target;
  stabilizer pruning is dropped wherever coordinates changed. Gates:
  known values (<2,2,2>: proves 7 in 0.03 s, refuses 8; <2,2,3>:
  refuses 12) and the recorded t=15 verdicts. Hardest t=15 root
  (1,1,1): 42.8 s / 96K tasks -> 13.3 s (memo) -> 0.31 s / 668 tasks
  — all level-2 nodes become leaves once the fans are 2^5 instead of
  2^8. t=16 root 0, depth 12, 30-min cap: still unresolved (exit 124)
  but the profile is now a search, not a thrash: all 28 level-1 folds
  expanded; 3,372 of 3,584 level-2 nodes evaluated (before: 12), 2,325
  Koszul leaves = the level-2 lemma's 72%; depth-3 fan 64, depth-4 32,
  depth-5 16; deep layers memo-dominated (depth 10: 6.1M hits vs 2.1M
  runs); 789 cap failures at depth 12 (was 181K at depth 8); 4.4M memo
  entries. Evaluated fractions per depth (94/81/71/76/49/39%) put the
  full root-0 tree at ~2-3x the 29 min done. Launched: t=16 on the
  fast root 1,10,64 (30-min cap; would be the first t=16 verdict), then
  root 0 with a 4-hour cap (t16_fastroot.*, t16_root0_long.*).
- **FIRST t=16 VERDICT (2026-09-02 ~09:00, 079ea49)**: with the Koszul
  wedge trimmed to the concise dimensions (a 3x4x4 residual builds
  tables over 3-4 coordinates, not 9: microseconds, not milliseconds;
  same flattening of the same honest tensor, sound), the pooled probe
  proves rank(T + m) >= 16 for root 1,10,64 in 6.1 s (415,993 tasks,
  261,384 early-aborted) — the same root timed out at 30 min an hour
  earlier with the 9-dim wedge, and every prior t=16 attempt since
  2026-08-31 (70 core-h, then 30-min caps x5) was unresolved. Gates
  before the run: <2,2,2> proves 7 / refuses 8, <2,2,3> refuses 12,
  recorded t=15 verdicts reproduced. The levers that compounded (all
  verdict-preserving, all gated): 12-core work queue, active-coordinate
  folds, fold-orbit pruning, subspace/tensor memo, CONCISION, depth 12,
  trimmed Koszul. Root 0 (the hardest, |Stab| 216) now running with a
  4-h cap (t16_root0_long.*); if it resolves, the full 211-root r=16
  rung is next.
- **r=16 UNSAT — EXHAUSTED: rank_F2(<3,3,3>) > 16, independent
  (2026-09-02 10:xx, r16_ladder.err)**: deep probe t=16, depth 12,
  pooled+concise+trimmed-Koszul, on all 211 true first-product orbit
  reps: 211/211 ok, 0 fail, 3,893 s wall on 12 cores (median 9.6 s per
  root, max 124.6 s; 367,575,689 tasks). Two rungs past yesterday's
  resting point in one morning, with no new mathematics: the wall was
  the probe evaluating concise 3x6x6 residuals in 9x9 coordinates
  (fans of 2^8 where 2^5 suffices, and a 6-ms wedge where a 6-us one
  suffices). Soundness chain per node: concision (isomorphism) ->
  cheap floors (flatten / Strassen / Koszul on the honest small
  tensor) -> substitution over active coordinates of the last pivot
  (all lambdas, one rep per stabilizer orbit where stabilizers are
  still valid) -> depth cap => 'unresolved' never 'proven'. Gates:
  known values, recorded verdicts, and the r=15 rung reproduced at
  ~100x lower cost. Next: r=17 (root 0 launched, 1-h cap, depth 13).
- **r=17 root 0: unresolved at 1 h, but a search in progress, not a
  wall (2026-09-02 midday, t17_root0.err)**: depth 13, 12 cores: 312M
  nodes run, 12 of 28 level-1 reps and 835 of 1,536 level-2 nodes
  evaluated (no leaves before depth 3 at these targets); memo grew to
  286M entries (~12 GB) — a per-shard entry cap with clear-on-overflow
  added (--memo-cap, default 120M). Extrapolating the level-1/2
  fractions, root 0 at r=17 is a few hours; the 211-root rung would be
  days at this rate unless the deep layers (depths 9-11: 260M nodes,
  memo hits 2x runs) shrink further. Relaunched with a 4-h cap.
- **r=17 root 0: unresolved at 4 h — the new wall, ~100x beyond the
  r=16 cost (2026-09-02 evening, t17_root0_long.err)**: depth 13, 12
  cores, memo cap 600M (126 shard clears — the key space exceeds the
  cap, so hits were lost): level-1 24/28 reps expanded, level-2
  2,937/3,072 evaluated, level-3 145K of 965K folds (15%) after 4 h;
  depth 7 alone 34M nodes (30% expanded). Extrapolation: ~1 day for
  root 0, weeks for the rung. NOTE root 0 was not the hardest root at
  r=16 (4.6 s vs median 9.6 s, max 124.6 s), so the rung is not
  rescued by easy roots. Where the work is: depths 8-13 (tiny concise
  residuals, targets 9..4) whose exhaustive substitution subtrees are
  re-derived because the memo churns. Candidate next levers, in order:
  (1) exact-rank TABLES for tiny concise tensors (all 3x3x3 over F2 by
  BFS from rank-ones: 2^27 entries, a 134 MB table; 2xnxn via the
  Kronecker/block-rank route) so depths >= 9 become leaves; (2) memo
  keys canonical under the small tensors' own GL symmetries; (3) a
  larger/hierarchical memo. The r=16 rung stands as the resting point.
- **Kronecker pencil oracle over F2 built; F2 breaks BOTH textbook
  facts (2026-09-02 evening, c83b292, src/pencil.rs)**: exact rank of a
  2 x m x n tensor via Kronecker structure (column/row minimal indices
  from block-Toeplitz nullities; elementary divisors from the Smith form
  over F2[x] of A + xB and xA + B) + per-block ranks BRUTE-FORCED
  (min_X rank X + rank(A+X) + rank(B+X); L_eps for eps <= 4, regular
  blocks of degree <= 5). Findings, all by brute force against random
  small pencils: (1) L_3 has rank 5 over F2, not Ja'Ja''s eps+1 = 4
  (the L block is multiplication of a linear form by a degree-(eps-1)
  polynomial; eps+1 evaluation points are needed and F2 has three);
  (2) regular blocks: irreducible cubic 5 (= D+2), (x+1)^4 6,
  irreducible quartic 6; (3) BLOCK ADDITIVITY FAILS: (x+1)^2 (+) N_2
  has rank 5, not 3+3 — so the block sum is UNSOUND as a lower bound
  over F2 (Ja'Ja''s additivity is for algebraically closed fields).
  Sound leaf actually installed (--pencil): sum of the blocks'
  algebraically-closed values + the single largest F2 excess (the
  cross-block substitution argument rank(P(+)Q) >= rank(P) + side-dim
  Q); exact brute force for pencils with m*n <= 16. --pencil-additive
  = the optimistic block sum, for measuring the leaf's ceiling only.
  Gates: 2x2 game value stays 7 under both; 3x3 root bounds unchanged.
  Ladder k=17..19 with --pencil launched (8-h cap,
  subgame_3x3_pencil.*): k=17 PROVED in 161 s.
- **Pencil-leaf ladder VERDICT: k=19 FAILS — the Koszul+{A,B}+pencil
  game still has exact value 18 (2026-09-03 02:xx,
  subgame_3x3_pencil.out)**: k=17 PROVED 161 s, k=18 PROVED 2,581 s,
  k=19 exhaustively refuted at 12,965,832 nodes / 22,437 s (6.2 h; the
  Koszul-only refutation was 6.79M nodes / 4.15 h — the pencil leaf
  costs nodes and lifts nothing at the root). The sound leaf (sum of
  algebraically-closed block values + one F2 excess; exact by brute
  force for m*n <= 16) is tight on 308/312 random small pencils, so
  the loss to non-additivity is not the explanation. Follow-up
  running: --pencil-additive (the optimistic block sum, unsound in
  1.6% of small cases) at k=19 to measure the leaf's CEILING — if
  even that cannot reach 19, the pencil direction is closed for 21.
- **Pencil CEILING verdict: k=19 FAILS with --pencil-additive too
  (2026-09-03 morning)**: 11,074,873 nodes / 26,660 s (7.4 h). The
  optimistic block sum overshoots the true rank in 1.6% of small
  cases, so this is an upper estimate of what any pencil leaf can do:
  NOTHING at the root of the Koszul+{A,B} game. Pencil direction closed
  for 21 regardless of additivity. Automatic follow-up running: k=19
  with --dump-frontier (3-h sample of the adversary's winning frontier)
  -> frontier_analysis.py (SAT exact-rank verdicts on the compressed
  small frontier states: leaf-limited vs genuine) ->
  frontier19_report.txt. (The "exact game value = 0" line in the
  additive output is a display artifact of running level 19 alone.)
- **FRONTIER VERDICT: the substitution game is MOVE-SET-limited, not
  leaf-limited (2026-09-03, frontier19.txt / frontier19_report.txt)**:
  a 3-h sample of the k=19 refutation (6.9M of its ~13M nodes) dumped
  822,622 refuted states (all prover moves failed; 783,417 distinct
  quotient tensors). Where they sit: depths 8-13, quotient dims
  (4,5,9), (3,4,9), (4,4,9), (3,5,9), ... — side C is never killed
  ({A,B} game), A and B are cut to 2-4 and 3-7; the gap k - leaf is 1
  (408K) or 2 (337K), rarely more. Exact-rank verdicts by SAT on the
  compressed small states (rank <= k-1; 24 samples per class, 60-s
  cap; the analysis hit its 2-h cap before the summary, 331 verdicts):
  213 GENUINE (a decomposition of rank k-1 exists: the adversary's
  kills really did push the rank below target), 5 LEAF-LIMITED (true
  rank >= k, Koszul one short; all in the (3,3,9) k=7 class), 113
  unknown (timeouts, concentrated in the 4-slice classes). Every
  2-slice class (2,n,9) is 100% genuine — consistent with both pencil
  leaves lifting nothing. READING: at the frontier the current leaves
  are already (almost) exact; the adversary's strategy is genuinely
  good there. A lift at the root would need a leaf that certifies the
  target at SHALLOWER states (5-6 slices x 5-7 x 9 at targets 12-13),
  where SAT already cannot decide 4-slice cases. Combined with the
  eight exhaustive FAILs in Wang's lattice (codim 3-4, table leaves),
  the value 18 of the Koszul+{A,B} game and Wang's 20 are properties
  of the substitution MOVE SET over F2, not of leaf strength; the
  route to 21 is new rules (coset/alignment dynamics, proven WLOG
  structure) or arguments outside substitution+flattening. Closed
  this week: pencil leaves (sound and optimistic), small-tensor leaf
  strength at the frontier.
- **Four-arm A/B on the 113 undecided frontier states — CORRECTS the
  frontier reading (2026-09-03/04, frontier_ab.py, frontier_ab/results.csv)**:
  each instance ("rank <= k-1" for a compressed 3- or 4-slice frontier
  tensor) under cadical, cadical + hand lex-leader on the products'
  (a,b) bits, kissat, and hydra_satsuma (Cook -> XOR/GE -> satsuma +
  kissat in Docker; the image was built for this), 300 s per call,
  12-way parallel, 4 x 113 calls. Verdicts: cadical 3 UNSAT / 1 SAT /
  109 timeouts; kissat identical; hydra_satsuma identical (its GE
  stage forced 108 of 1,278 variables but satsuma did not convert the
  product-permutation symmetry into speed); cadical+lex 47 UNSAT / 0
  SAT / 66 timeouts, solve times 0.3-267 s. Zero SAT-vs-UNSAT
  disagreements across arms. Decided instances by slice count: 3-slice
  32 UNSAT + 1 SAT (11 open), 4-slice 14 UNSAT (54 open), 2-slice 1
  UNSAT. READING CORRECTION: the earlier 213-genuine sample was
  dominated by 2-slice and tiny 3-slice states; at the mid-size
  frontier (3 x ~6 x ~7 at targets 7-10, 4 x ~6 x ~7 at target 9) the
  decided states are 47 of 48 LEAF-LIMITED — their true rank meets the
  target and Koszul is one short. So the substitution game is
  move-set-limited at the small end and LEAF-limited at the mid-size
  end; a leaf certifying 8-10 on concise 3-4 x 6-7 x 6-7 tensors would
  invalidate the adversary's refutations there (whether the root then
  reaches 19 is a new question). Cost reality: 783K distinct frontier
  tensors in the 3-h sample; lex-SAT decides one in 0.3-267 s; the GL
  orbit count of concise 3x6x7 tensors over F2 is ~2^26, so neither a
  table nor per-node SAT is a leaf — it needs a cheap bound that closes
  a gap of exactly one on these shapes. Measured lever for exact rank
  by SAT: hand lex-leader (47 vs 3); not kissat, not satsuma.
- **The pooled probe as a frontier leaf: sound, cheap, certifies ~40%
  (2026-09-04, --probe-tensor-file, frontier_probe*.out)**: the 331
  sampled frontier states (52 leaf-limited by SAT, 214 genuine, 65
  open) run through schemesearch3's pooled probe (concise, ALL three
  sides — the {A,B} game never kills C, and at a (3,4,9) state side C
  still has dimension 9 — trimmed Koszul, memo) at target k. Depth 6,
  2M-task cap: genuine 0/214 certified (negative control holds);
  leaf-limited 19/52; open 25/65 (4 capped). Median 0.0 s, max 4.5 s
  per state. Depth 10, 20M cap, on the 73 non-certified: +1
  leaf-limited, +8 open, the other 64 EXHAUSTED (full tree, no proof)
  — depth is not the limit; those states are beyond bounded
  substitution + Koszul from any side. Totals: leaf-limited 20/52,
  open 33/65, genuine 0/214, zero unsound. By class the probe helps
  where sides are balanced ((4,4,9) 9/14, (4,6,9) 12/20) and not where
  a side has dimension 3 ((3,3,9) 0/8, (3,4,9) 3/12 at depth 6): the
  (3,4,9) k=8 class stays the "gap of one" test set. Decision pending:
  installing the probe as a budgeted leaf in subgame (the pool lives in
  schemesearch3.rs; a library refactor of ~1 day) and rerunning k=19 is
  the experiment that says whether the root moves.
- **Probe leaf in the game, run 1: CAP at 12 h (2026-09-05,
  subgame_3x3_probe.*)**: the probe engine moved into the library
  (src/probe.rs; schemesearch3 is a thin binary; both gates
  reproduce), subgame --probe-leaf D / --probe-cap N / --probe-min-dim M
  (pooled probe at the target on states with a side of dimension <= 4,
  memoized per canonical state; 2x2 gate: 7 proved, 8 refused). k=19
  with Koszul + {A,B} + pencil + probe(depth 6, cap 200K tasks):
  CAPPED at 42,000 s / 6,549,345 nodes, no verdict. Probe: 2,124,162
  calls, 1,247,003 certifications (59%). Cost: the node rate fell from
  ~185K per 10 min to ~22K as the search reached regions where the
  non-certifying 41% of calls ran to the 200K-task cap (~0.8 s of a
  thread each). Equal-node comparison (6.5M nodes): pencil-only run had
  667K refuted states at 8,400 s; this run 819K at 42,000 s — the
  probe changes the tree's shape but the root question stays open.
  Run 2 launched: probe depth 5, cap 20K tasks (about 10x cheaper per
  non-certifying call; the frontier test showed depth beyond 6 adds
  little), 24-h ceiling (subgame_3x3_probe2.*).
- **Probe leaf in the game, run 2: k=19 FAILS — exact value 18 under a
  FOURTH rule set (2026-09-05, subgame_3x3_probe2.out)**: Koszul + {A,B}
  + pencil + probe(depth 5, cap 20K tasks): exhaustive refutation at
  8,280,527 nodes / 32,095 s (8.9 h). Probe: 2,771,435 calls,
  1,580,481 certifications (57%) — the leaf certified 1.58M states the
  game could not, and the adversary routed the refutation around all
  of them. Reading: the root value 18 is not a property of any leaf we
  can build from bounded substitution + Koszul from any side; the
  adversary's winning strategy passes through states that are
  genuinely below target (the small end of the frontier) or beyond the
  probe (3-dimensional-side classes). Next decisive, cheap test: the
  probe on the codim-3 children of Wang's six stuck codim-2 orbits at
  target 18 (his table value 17) — condition 3 of the route to 21.
- **Condition 3 FAILS: the probe cannot reach Wang's lattice values,
  let alone lift them (2026-09-05, wang_orbit_probe.*)**: all 14
  codim-2 and 68 codim-3 orbits of his table (quotients T|ker U,
  7x9x9 and 6x9x9) run through the pooled probe at depth 8, 20M-task
  cap, both at table+1 (lift) and at the table value (control): 0 of
  164 certified — 160 exhausted (full tree, no proof; most in under 2
  s), 2 capped, max 125 s. The probe does not even reproduce his 18s
  and 17s: his DP proves them by full-depth substitution memoized over
  the orbit lattice, while a depth-8 probe from target 18 must prove
  targets 10-11 on residuals that still have two 9-dimensional sides,
  which its leaves cannot do. It certified our game's frontier
  because those states had targets 7-10 at dimensions 3-4 on every
  side. VERDICT on the route to 21 via the probe: closed. Standing
  results: game value 18 under four rule sets; Wang's 20 unmatched by
  anything we built; the leaf-limited frontier of our game is real
  but irrelevant to his lattice's frontier, which sits at targets
  15-18 with two full sides. What remains for 21 is items 3 and 4:
  new move rules with content (coset/alignment dynamics, proved Rank
  Law case splits) or arguments outside substitution + flattening.
- **THE CODE BOUND: an F2-specific LP lower bound; rank >= 16 at the
  root by one LP with an exact dual certificate; the r=16 rung by 263
  LPs (2026-09-05, matmul/r22/code_bound.py)**: in a decomposition
  T = sum_i a_i x b_i x c_i concise on a side of dimension k, the
  covector phi's slice T(phi,.,.) is the sum of the rank-one matrices
  of the products with phi(a_i) = 1, so |S_phi| >= rank(T(phi,.,.));
  over F2 the map phi -> S_phi is linear and injective, so {S_phi} is a
  k-dim binary linear code in F2^r whose weights are bounded below by
  slice ranks. With m_c = number of products of coefficient type c:
  rank(T) >= min sum_c m_c s.t. sum_{c: <c,phi>=1} m_c >= rank(T(phi,.,.))
  for all phi != 0 — an LP/ILP in 2^k - 1 variables, max over sides.
  The coset bound is the special case "all slice ranks >= 3". Root:
  LP 15.75 on every side; the rationalized dual (max column load
  257/256) gives the EXACT bound 4032/257 = 15.69 => rank >= 16, a
  certificate checkable in integer arithmetic. Gates: <2,2,2> and
  <2,2,3> below their known ranks (see the run log). Measurements:
  all 263 level-1 residual tensors (all 211 true orbits) >= 16 by LP
  (the r=16 rung in seconds; 3,893 s by search); the 256 folds of a
  root: 240 at 16, 16 at 15 (the rank-1 killers) — r=17 may reduce to
  16 recursions per root; Wang's codim-2/3 orbits: 13-15 vs his 17-19
  (not a lattice lift). Next: a rigorous LP leaf in the probe (solve the
  dual, rationalize, exact bound) and the r=17 rung.
- **LP-pruned recursion for r=17: the code bound prunes 76-97% per
  level but a side-A-only chain bottoms out on genuinely low pencils
  (2026-09-05 late, lp_recursion.py, lp_rec_*)**: folded-side LP only
  (the two 9-dim sides never certified a fold and cost 27x more), LP
  leaf at every level, all 263 residuals in 12 shards (~60 s per
  root). LP-leaf rates by level for root 0 at target 17: 240/256,
  1926/1984, 3162/3520, 6980/8734, 13824/18104, 9200/15294; 5,274
  pencils deferred at target 10 per root (560,118 over all roots).
  Pencil batch: 244,969 certified by the Kronecker oracle + 4,153 by
  the probe; 310,996 EXHAUSTED (56%) — the surviving chains are the
  adversary's rank-1 kills and end in pencils of rank < 10, so a
  single-side chain cannot prove the rung (the r=16 rung was proved
  by the probe SWITCHING sides where side A failed). Cutoff 11
  instead (3x9x9 at target 11 to the all-sides probe): 400-node
  sample 98 certified / 118 exhausted / 184 capped at 500K tasks.
  Conclusion: the LP must be a leaf INSIDE the side-switching probe;
  that needs a fast, correct LP in Rust (the in-tree simplex is 185 s
  at 511 variables and stalls on this degenerate 0/1 LP; HiGHS via
  the highs crate is the route, cmake permitting).
- **Code bound as a probe leaf via HiGHS (2026-09-05 night)**: cmake
  installed at user level (pip), highs crate built; code_bound in
  probe.rs solves the dual packing LP with HiGHS and keeps the exact
  rational certificate; values match Python exactly at 0.1-0.4 s per
  LP (root 16 in 0.36 s; the in-tree simplex took 185 s and stalled).
  --code-leaf: gates pass (known values; recorded verdicts — the LP now
  certifies the roots at 15 and 16 with 0 tasks). r=17 root 0, depth
  12, 30-min cap: CAPPED, but the tree's top is collapsed — level-1
  folds 10/12 code leaves, level-2 61/64, level-3 134/156, level-4 20
  code + 409 Koszul/Strassen of 507 — while the middle (depths 6-11,
  4-6-dim sides at targets 11-13) still holds 20M+ nodes with the code
  leaf certifying only 10-15% there (consistent with its 5/117 at the
  frontier). Only 2 of ~28 level-1 subtrees were entered in 30 min;
  a 4-h run on root 0 is measuring the full per-root cost. Reading so
  far: the LP moves r=17 from ~1 day/root (previous attempt) toward
  hours/root — a ~10^3-core-hour rung, cluster-scale, not Mac-scale —
  unless a mid-size leaf appears.
- **FIRST r=17 VERDICT: root 0 proves rank(T + m) >= 17 in 2.75 h with
  the code-bound leaf (2026-09-06 early, t17_root0_code4h.*)**: pooled
  probe, concise, all sides, trimmed Koszul, memo (70M entries, no
  clears), HiGHS code bound as a leaf after Koszul: 9,882 s on 12
  cores, 74.0M tasks run, 66.1M skipped. Profile: levels 1-3 almost
  entirely code-bound leaves (24/28, 491/512, 1148/1240); the work is
  at depths 7-11 (2M / 7.9M / 20.8M / 28.0M / 14.3M nodes), where the
  code leaf still certifies 0.3-1.3M nodes per level and Koszul the
  bulk. The same root was unresolved at 70 core-h (2026-08-31), at 4 h
  with concision (2026-09-02), and at 4 h with concision + memo
  (2026-09-05). PRICE of the r=16->17 rung: ~33 core-h per root x 211
  = ~7,000 core-h if root 0 is typical (it was average at r=16) — a
  cluster afternoon at 1,000 cores, ~24 days on this Mac. Second root
  (1,10,64): PROVED at r=17 in 1,542 s (26 min, 1.02M tasks) — 6.4x
  cheaper than root 0; per-root cost spans 0.4-2.75 h on two samples,
  so the rung is ~2,500-7,000 core-h (9-24 Mac-days).
- **THE LATTICE INTEGER PROGRAM: 20 or 21, undecided after 40 min
  (2026-09-06, lattice_ip.py, lattice_sat.py)**: variables m_c = number
  of products with A-coefficient c (511); constraints from Wang's
  verified table, sum_{c not in U} m_c >= t_U for every vector (all 19)
  and every 2-dim subspace (11,417 at 18, 32,018 at 19; labeled by
  --lattice-values), plus the slice-rank (code-bound) rows; objective
  min sum m_c. Sound: products with a_i in U vanish in T|U. LP
  relaxation 19.09 -> 20 (= Wang's DP by integrality on codim-1);
  HiGHS MIP: incumbent 21, dual bound 20 at the 40-min limit. At r = 20
  the program is boolean (each type at most once): a 20-set of vectors
  with no two in a 19-pencil, no full 18-pencil, and >= 3 rank(phi)
  members pairing to 1 with every covector phi. The pairwise condition
  alone does not bite (clique number of the 18-pencil graph is 57:
  rank-1 vectors are universal, every pencil containing one is an
  18-orbit); the slice-rank counts are the binding part (rank-2 phi
  need 6 of 20 where a rank-1 type pairs to 1 with 16 of 49). Running:
  cadical on the 20-set CNF (30-min cap) and the MIP for 4 h. UNSAT /
  optimum 21 would be a NEW THEOREM: rank_F2(<3,3,3>) >= 21 from
  Wang's certificate plus this counting; SAT would exhibit the
  20-configuration and say which further constraint (codim-3 values,
  B/C-side types) to add.
- **Lattice IP at codim <= 2 has optimum 20; codim-3 kills the witness
  (2026-09-06 evening)**: cadical on the boolean 20-set formulation
  (32.9M vars with sequential counters, 65.9M clauses): SAT in 111 s —
  S = {2,4,7,8,11,13,14,32,63,128,144,192,195,216,219,260,288,325,
  360,448}: 17 rank-1 and 3 rank-2 A-types. So Wang's codim-1 and
  codim-2 values plus the slice ranks do not force 21. Checked against
  his codim-3 values on the 1,080 subspaces spanned by S's own triples:
  2 violations (17-orbit subspaces containing 4 of S where at most
  20 - 17 = 3 are allowed). Running: the labeling of all 788,035 3-dim
  subspaces (--lattice-dim3; 68 table orbits, values 15-18) followed by
  the SAT with codim-3 constraints (at most 20 - t_U of the 7 vectors of
  each U). UNSAT there = rank >= 21 from Wang's certificate + counting.
- **Codim-3 lattice SAT: still a 20-set (2026-09-06 night)**: with all
  788,035 codim-3 values added (at most 20 - t_U of the 7 vectors of
  each 3-dim U; CNF 93.3M clauses) cadical finds a 20-set in 139 s:
  {1,3,6,8,18,33,35,54,56,63,64,73,161,177,195,216,384,432,504,511} — 16
  rank-1, 2 rank-2, 2 rank-3 A-types. So Wang's verified A-side values
  through codim 3, combined by counting across all children at once,
  still admit 20; the witnesses resemble real schemes (Laderman-like
  rank-1-heavy A-factors). Trend: each level kills the previous
  witness and admits a new one — the A-side hierarchy converges to his
  20, not past it. Untested extension that uses what his framework
  lacks: the JOINT two-side model — variables m_{(a,b)} over pairs of
  A- and B-types (511^2), constraints from doubly restricted tensors
  sum_{a not in U_A, b not in U_B} m_ab >= LB(T|U_A,U_B) (LB by code
  bound/Koszul on the 8x8x9 restrictions; 261K codim-(1,1) pairs) plus
  the per-side lattice rows. A day of work; the mixed-game FAILs say
  mixed leaves are flattening-class there, so the expectation is low.
  Codim-4 on the A side alone (3.3M subspaces, counters not clauses) is
  the other option; by the trend it would admit 20 as well.
- **Joint two-side lattice model: dead on arrival, by arithmetic
  (2026-09-07)**: with per-type counts on sides A and B and pair counts
  m_ab, the row for a doubly restricted tensor reads
  r - m_A(U_A) - m_B(U_B) + m_AB(U_A,U_B) >= LB(T|U_A,U_B). At r = 20
  with each type used at most once, a codim-(1,1) row can bind only if
  LB(T|v,w) >= 19 and a codim-(2,2) row only if LB >= 17 (two used
  types per pencil, the most the A/B codim-2 rows allow). Measured: the
  code bound on T|v,w (8x8x9) is 14 on every sample, on T|U_A,U_B
  (7x7x9) 11-13; Koszul is lower; the mixed game's exhaustive FAILs put
  every mixed leaf in the flattening class. Gaps of 4-5 at every level:
  no joint row can bind, so the joint model adds nothing to the A-side
  hierarchy, which itself converges to Wang's 20. Time-box closed at
  ~1 h of analysis instead of a day's build. The lattice counting idea
  is therefore fully explored: it reproduces 20 (integrality on codim-1)
  and cannot pass it with any bound we can certify on restrictions.
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
- **d-profile scan of the full DB (2026-10-10, `matmul/dprofile.py`,
  6.5 s)**: per class, d = distinct factors per side (mod 2), giving the
  basis-invariant Karstadt–Schwartz-model floor dA+dB+dC−13 (each input
  leg ≥ d−9; output leg ≥ d−9+14 by transposition) — the cost model of
  Nielsen's 52-add scheme (arXiv 2609.06588; our Lean check commit
  db1217b). All 17,376 schemes: floor histogram 47:44 48:507 49:2450
  50:5431 51:5645 52:2727 53:513 54:58 56:1 (Laderman (23,23,23)).
  **Global floor = 47, attained by 44 schemes incl. our 55-record class
  i19w225c4efh (d=(20,20,20) — matches flip23 census "shared 9" = 3
  pairs/slot), Nielsen's own i12w195c23ci (also (20,20,20); his 52 has
  5 adds of floor slack, output 28 vs leg-floor 25), Stapleton's
  i2w201c26fi, and our 60-add i106/i107 classes (side d=19, the DB
  max sharing).** Verdict: counting does NOT exclude ≤52 for our class
  (pre-scan prediction of a 53–54 floor was wrong — the d≤22 inference
  from exact side 13 only bounds one way; gate caught it). Next stage
  if pursued: exact free-basis leg minimizer (min over invertible B of
  adds(X·B), sidemin-style IDDFS from a chosen 9-basis) on the three
  legs of ours + Nielsen's class; 51 anywhere = outright record in his
  model. CSV regenerates from dbcache/schemes.tgz.
- **Free-basis leg minimization EXACT on both 52-candidate classes
  (2026-10-10, `src/bin/fbmin.rs` + `matmul/fbmin_legs.py`, 2 threads,
  ~15 min)**: per leg (23×9, d=20), a = (d−k)+h over k basis-targets
  and h helpers; tier sweeps (closure of 9-target bases; +1 helper at
  the fixpoint / 8-target+free-vector; the a=13 tier with 2 helpers /
  8T+g+h / 7T+2g) are complete by the fixpoint-injection lemma, every
  "yes" carries a replayed chain certificate, every "no" is exhaustion.
  **Our i19w225c4efh: A=13, B=13 (2 helpers), C=12 ⇒ exact KS-model
  per-step minimum 13+13+(12+14) = 52, down from flat 55. Nielsen's
  i12w195c23ci: A=12, B=12 (= his published sides, certs), C=14
  (854 s exhaustion) ⇒ his 52 = 12+12+(14+14) is EXACTLY optimal for
  his class.** Both tensors tie at 52; no 51 on either. Gates: his
  published 12+12 reproduced + proven optimal; our flat A=13 proven
  basis-optimal. Caveats: F₂ chains (sign-lift to general fields
  pending, as in his §lifting); legs decouple so sums are exact.
  OPEN: 51 needs another class — floor-47 club has 36 unswept names,
  and the 2,528 schemes with a d≤19 side have leg floors of 10;
  ~30 min/class at 2 threads with fbmin as-is.
- **★ 51 FOUND (2026-10-11, fbsweep ~30 classes in): class
  i12w211c23fg (HKS family 17x2+52x+4y6+5y4+14y3+z32+2z27, Nielsen's
  own family) has exact free-basis legs 12+13+12 ⇒ per-step total
  12+13+(12+14) = 51 over F₂ — one below Nielsen's 52, and EXACT for
  the class (tier exhaustions per leg). Independently replayed
  single-threaded, certificates archived matmul/external/ks51/.
  Also so far: tie-52 classes i12w199c23ci (13+12+13), i12w211c26fi,
  i12w239c28aj, i12w243c3bcf; 53s incl. Stapleton's i2w201c26fi
  (13+13+13); the deep-sharing i106/i107 classes all ruled out
  (sums ≥ 40). Sweep continues (50 would need legs 12+12+12).
  PENDING for a ring-valid 51: sign-lift of this class's certs
  (fblift pipeline; lift_models for alternative sign models).
- **S-P 51 Lean-verified (2026-10-13, commit 783d433,
  proof/Mm/SP51.lean)**: Stapleton–Perminov's published scheme
  (arXiv:2609.32388) transcribed verbatim from their paper listing
  (matmul/external/sp51/), gated by gen_sp51_lean.py on the published
  accounting (counted 13+12+26 = 51, conversions 1+3+1 = 5 uncounted,
  one-shot 56), P/Q/R unimodularity, and a word-ring ℤ⟨A,B⟩ replay;
  axioms [propext] / standard, abel fallback needed (pure-reorder
  outputs). Both ring-valid 51-packages with known conversions are now
  kernel-checked (ours 51+11, theirs 51+5). QUEUED on supplemental
  sweep completion: paper update — four-51 table (lift status +
  conversion minima), family analysis (all four in i12 =
  17x2+52x+4y6+5y4+14y3+z32+2z27; name grammar verified: i = family
  index, w = cubic-term count, family string = rank invariants
  x/y/z), final sweep census, SP51.lean in §verify, plus any new 51s
  the sweep's tail yields.
- **SWEEPS COMPLETE + CENSUS FROZEN (2026-10-13 evening, ac4cd9f;
  CSVs archived matmul/external/ks51/fbsweep*_final.csv)**:
  supplemental 258/258, no new 51s beyond the four (2×51 = S-P -008 +
  -012, 13 tie-52, 35×53, 18×54, 190 ruled-out; ten families, no 51
  outside i12); main timeout class i110w205c238h closed by leg-floor
  arithmetic (15+14+(d_C−9=10) = 39 > 37) ⇒ database ≤51 settled
  unconditionally, no 50 anywhere (min non-51 leg sum 38);
  floor-achieving legs now 32 of 1,079 exact (d = 20, 21, 22).
  mint50 auto-started (11 threads, 28 seeds). Remaining paper items:
  overnight race verdicts (due ~7:20 AM Oct 14) into §signs +
  open-problem (1), then Zenodo v2 (final PDF + frozen CSVs).
- **2026-10-14 morning (9810e0e +)**: free-vector race CONCLUDED —
  all three 24 h arms timeout, 0 verdicts, 8 configs total; §signs
  final. **No 50 in the DB at ANY floor**: 0/2,450 floor-49 schemes
  all-legs triple-clean (necessary condition), floor ≥50 arithmetic,
  floor ≤48 swept — any 50 lives outside the published DB; paper
  §sweep carries the argument. Walk-52 census: 59 mint 52s = 20
  classes, 17 of the DB's 27 tie-52 classes + 3 NOT in the DB (novel;
  reps walk-00123/01012/+1, exact IDs pending). Mint v2: screen keeps
  floor-49 all-clean shapes; 27 DB tie-52 reps added (55 seeds);
  relaunched after clean STOP. TODO: archive novel-52 reps to
  external/ks51/new52/ + equivalence-crawl them vs our 123-corpus;
  Zenodo v2.
- **2026-10-14 (52-stratum transform bounds, queued for paper)**:
  light-row lower bound (at slack s the basis needs k ≥ 9−s target
  rows; conversion ≥ Σ(weight−1) of the k lightest targets) gives
  conversions ≥ 8 for ALL 27 DB tie-52 classes (min 8 =
  i2w205c38hj) and ≥ 5/≥ 8/≥ 7 for the three novel classes ⇒ no
  52-class known can convert for ≤ 3; one-shots ≥ 57 everywhere ⇒
  the 52-stratum cannot threaten flat-55 or S-P's 56 one-shot.
- **DESIGN-FIRST PROBE CONCLUDED (2026-10-15, three measured
  negatives)**: (1) completion machinery sound — a known frozen
  A-design completes in 3 ms warm-started (anf --init-file; cold
  >80 s); (2) design mutation 0/300 — single re-parents of the known
  11-leg DAG leave a tight ~9-equation defect (floor-achieving
  designs are ISOLATED, cf. Q-flip rigidity); (3) abfix 0/5,000 —
  uniform B-designs never pair with the true A (defect ~25, linear-C
  decided). VERDICT: legs cannot be decoupled; Brent's cross-leg
  coupling binds, which is why i12's coincidence structure is
  special. Remaining 50 routes: flip-move walking (held) or a
  structural lower bound. Tools kept: design50.py modes a/ab/abfix,
  anf --init-file. (Caveat added 2026-10-16: stage-1 sampling drew only
  isolation-0 designs; floor legs with an unused generator exist, 5/32
  observed, and were never sampled. The verdict is heuristic anyway.)
- **★ FIRST CYCLIC-INVARIANT RANK-23 SCHEME OVER F2 (2026-10-15,
  commit 182fd57)**: the symmetric-quotient attack (cyclic 3-cycle,
  207 orbit vars, product ansatz 7 3-orbits + 2 fixed with a=b=c)
  is SATISFIABLE -- kissat decides it in ~1 min where the full
  621-var Brent CNF is classically CDCL-hostile; the quotient makes
  3x3 tractable. Solution full-verified (0/729) + invariance
  confirmed; NO cyclic-invariant scheme existed among all 37,204
  known. Sol-1 legs d=21 iso=3 (the "iso=3 => per-step >= 53"
  inference first written here was WRONG -- see the 2026-10-16
  cyclic-screen correction below). Encoder gated on exact 2x2x2
  values (SAT@7/UNSAT@6). symenum.py enumerates with blocking on the
  207-rep projection, screens each leg: d=21 floor-attaining leg
  (12 adds) = a 50; d=20 floor leg = a 47. HUNT RUNNING.
- **CORRECTION + closeout (2026-10-16 evening, 9ac7285)**: the
  "isolation 0 is necessary for a floor leg" claim was false (5/32
  floor legs have an isolated row); the floor-49/50 no-50 screen that
  relied on it was re-run EXACTLY with fbmin --tier1-only over all
  7,881 schemes: none qualifies, so no-50-at-any-floor stands. Hunts
  wound down to a trickle (flipmint 2 threads, census 1). Cyclic-50
  decisive instance (symshape.py) built; gate's UNSAT side intractable
  for kissat (pinned to census schemes sym-00006/sym-00001, both
  fbmin-certified leg 13: A=13 SAT in 8.6 s / 24.5 s, A=12 hit the
  30-min cap on both, where fbmin decides the same question in ~6 s),
  so the unpinned instance is out of reach for plain CDCL. Zenodo v2
  kits ready (ks51 v2.0, mm55 v1.1), awaiting Greg's tags/upload.
  CYCLIC-SCREEN CORRECTION: symenumd skipped d=21 schemes with iso>=3
  (the same false isolation inference); a d=21 floor leg needs only
  >= 12 non-isolated rows (iso <= 9). Fixed in symenumd (census
  restarted with preblock, 140 kept). New matmul/symcheck.py decides
  "A-leg <= 12" exactly per scheme (d=21 --tier1-only, d=20 tiers 1-2)
  after a full-Brent re-check: all 170 distinct cyclic schemes from the
  three census runs have A-leg >= 13, i.e. per-step >= 53 -- now exact
  (the 39 skipped included). Schemes archived (they lived only in
  /tmp): matmul/external/cyclic/census{1,2,3}/ + cyclic_check.csv.
- **ZENODO KS-51 v2.0 PUBLISHED (2026-10-17)**: doi:10.5281/zenodo.23441986
  (https://zenodo.org/records/23441986), a new version under concept
  doi:10.5281/zenodo.23305910, which the paper cites. Paper dated
  2026-10-17, draft marker removed, Appendix A retitled, Appendix B
  (kernel_optimal_for_class sketch) added; tag v2.0-ks51 = da2b9c0
  pushed. mm55 v1.1 kit (doc/zenodo_mm55_v1.1.md) still pending.
- **BOTH PAPERS SUBMITTED TO arXiv (2026-10-17)**: KS-51 as submit/8246158,
  the 55-addition paper as submit/8246196; primary cs.MS (Greg's endorsed
  category; cs.DS needs an endorsement he lacks), cross-listed cs.DS,
  cs.SC, cs.CC; ACM F.2.1; G.4; I.1.2; arXiv non-exclusive license.
  Expected announcement Mon 2026-10-19 20:00 ET. The KS-51 paper gained
  an Acknowledgments section disclosing the AI-assisted collaboration
  (492bfc7; arXiv policy requires reporting generative-AI use), which the
  Zenodo v2 PDF lacks. Metadata as submitted: doc/arxiv_kit.md.
- **3×3 TRACK CLOSED (2026-10-17, Greg's call)**: all 3×3 compute
  stopped (CEGAR production run, flipmint, waiters). Standing results:
  flat 55 (unique in the HKS DB), KS-model 51 for our class
  i12w211c23fg (ring-valid, model 21; exact for the class), exactly four
  51-classes in the DB and no 50 at any floor, S-P's 51 class-optimal
  in Lean (SP51Optimal), three novel ring-valid 52 classes; both papers
  on Zenodo and submitted to arXiv. Final numbers of the last runs:
  CEGAR cegar12 (outputs committed): 244 certified cores, 7 refuted
  schemes (all in the first hour), then every worker's solve ran
  72,600 s with no model; the 639-cube split closed none; cyclic-50
  stays OPEN with strong negative evidence (census: 170 distinct cyclic
  schemes, all per-step >= 53, exact). Flip hunt: flipmint 331 and
  mint50 619 schemes evaluated exactly, min leg sum 37 (= 51); all 16
  ALERT-51s are the four known classes (matmul/external/ks51/
  alert51_classes.csv), no 50, no new 51 class. Result CSVs in
  matmul/external/ks51/{flipmint,mint50}_results.csv; corpora kept on
  disk, gitignored: matmul/found23flip/ (24,592 schemes),
  matmul/found23mint/ (9,931). Open questions are the KS-51 paper's
  §open list. Next track: 4×4 rank-47 F₂ XOR count (record 170).
- **4×4 RANK-47 F₂ XOR COUNT: 168 < 170 (2026-10-17)**: record 170 =
  PLinOpt data/4x4x4_47_mod_2 (L 44 + R 44 + P 82; cited by
  arXiv:2609.12027). New src/bin/xor47.rs (randomized Boyar–Peralta,
  exact 2^16 distance table, P side via its transpose + Tellegen, which
  adds 31) gives **168 = 44 + 44 + 80 on the same scheme**, verified by
  matmul/x47/x47check.py (matrices + 256-pair Brent) and PLinOpt
  SLPchecker -q 2; files matmul/x47/best/x168/. Orbit search (GL(4,2)^3
  + slot symmetries, coordinate descent): reference class 168,
  AlphaTensor-47 169 (from 179), KM-47 169 (from 186). Pilot lookahead
  (width 16) does not move the reference sides (44/44/49). All three
  classes are flip-isolated; a rank-47 walk with ±2 excursions found
  nothing new. Instance floor (distinct non-unit targets + 31) = 139 for
  the reference.
- **4×4 RANK-47 XOR: 167 (2026-10-17, c4e4243)**: simulated annealing on
  the orbit (elementary-matrix moves, BP-scored) reaches 168 in every
  chain of every class (24/24 ref, 24/24 AlphaTensor, 23/24 KM) -- a
  universal BP plateau. New exact helper search (cost = |targets| + h
  non-target signals; closure + iterative deepening on h; exact) proves
  BP optimal at an AlphaTensor 168 point (44/48/45) but finds BP 50 -> 49
  on the expensive side of KM points: **167 = 44 + 49 + 74**
  (matmul/x47/best/x167, both checkers). Pipeline now: anneal with
  --collect (all points <= 169: ~14k collected) -> refine (exact per
  side, cached by target set). First 136 KM refinements: 44 at 167, none
  at 166 yet. Reference L: exact h <= 5 impossible (L >= 43, BP 44); h = 6
  out of reach; helper-pool LNS inconclusive.
- **4×4 XOR: EXHAUSTIVE ORBIT SCANS + EXACT SETTLING (2026-10-18)**:
  xor47 scan (side costs invariant under permutation matrices on each
  sandwich factor → 840 cosets; three 840² BP tables + min-plus over
  840³; slot symmetries redundant): orbit minimum under BP = 168 in ALL
  three classes (KM 2, AT 13, ref 2 coset triples). Exact core v2
  (incremental closure, full canonical helper order, undo; ref L h<=5 in
  23 s vs 282 s) + xor47 settle (side cache): depth-6 pass on triples
  that could reach 166: 144 sides, 137 BP-optimal, 4 improved by one (KM),
  3 unresolved. No triple below 167 anywhere; open (lb <= 166, a side
  needs >= 7 helpers): KM 7, AT 0, ref 78. S3-symmetric SAT (s3cnf.py):
  rank 49 (4,8,0,1) SAT in 6 min; rank 47: 8 h pool over 144 shapes, no
  scheme, 53 UNSAT (cadical, unchecked), 91 open. Paper draft updated.
- **4×4 RANK-49 ALL-RINGS SCREEN (2026-10-18): no point below 156**
  (matmul/x49/README.md).  Target: PLinOpt's 156 (5+8/11), valid over
  every ring; F₂ costs bound signed programs from below.  Strassen²
  class: orbit-scan minimum 156; all 1291 coset triples within +2
  refined exactly (36 at 156, rest 158, BP optimal on every side; the
  whole orbit is proved in the next bullet).  July F₂ corpus: 5 sampled schemes not
  ±1-liftable; screen stopped at 36/2012 (best 156, r49-20127, lift
  untested).  New integral family, mixed-inner Strassen (mixed.py: each
  outer product gets its own inner scheme from Strassen's 36-element
  orbit): 200 members, `xor47 screen` histogram 156:1 157:22 158:82
  159:79 160:13 161:3; exact orbit scans of the top five: 156, 157×4.
  The 167 went to PLinOpt as jgdumas/plinopt PR #22.  MMchecker -q 2 is
  one random F₂ test per run (a corrupted copy passed 31/40), so
  correctness rests on x47check.py's 256 basis pairs.
- **★ STRASSEN² CLASS PROVED >= 156 (2026-10-18)**: new `xor47 lbscan`
  (whole-orbit lower bounds: per coset pair, distinct non-unit targets
  plus one if the inputs' closure misses a target, then exact helper
  levels only for target sets in a triple that could still fall below
  the target; min-plus over all 840^3 triples).  Strassen², rank 49:
  PROVED in 1 s with no exact search: 22,284 triples have target counts
  summing to <= 123, the closure term lifts all but 36, and those 36 are
  exactly refine49's 156 points.  Independent matmul/x49/lbcheck.py (own
  GL/cosets/closure, Brent check of the action with a negative control,
  coset-table check) agrees; both tools fail at target 157.  So the
  all-rings 156 cannot be beaten inside this class without a change of
  basis.  Correction: `settle` cannot close a window gap (it only
  re-solves open sides inside the refined window); lbscan does.
- **KM CLASS WHOLE-ORBIT BOUND >= 163 (2026-10-19)**: lbscan on
  seeds/km47 (matmul/x47/README.md, lbkm/).  Cheap bounds 144; levels
  1-2 on 1.5M sets 150; aiming at 167 directly needs ~10^5 level-3 sets,
  so lbclimb.sh raises the target one step at a time on a shared
  checkpoint (tens of deep sets per step): 151..163 proved (161: 1.9 h,
  162: 3.2 h, 163: 6.6 h with level-5/6/7 refutations), the last
  steps with level-5/6 refutations (3-60 min each, parallel search; 1-
  thread level-5 tests timed out, hence one-at-a-time parallel mode).
  Older-search cross-check (lbcheck1): 200/200 level-4, 8/8 level-5
  refutations, 51/51 exact sets.  The 167
  paper's "no triple of any class drops below 167" is window-scoped:
  reword as "near-minimal triples" plus the whole-orbit bound.
- **RANK-49 MIXED FAMILY SCREEN (2026-10-19): no candidate.**  1,200
  mixed-inner Strassen members (200 + 1,000 new, seed 2) each through
  `lbscan --target 156` (matmul/x49/lbscreen.sh): all 1,200 PROVED >=
  156 over their whole orbits, 1.5 s each (closure test + one-helper
  refutations suffice), 32 min total; control at 157 on mix-00084
  reports its 156 point.  Together with the Strassen^2 proof: nothing
  tensor-like we can generate beats 156; a record needs a new integral
  rank-49 class.  AT and published rank-47 climbs chained next.
- **MOD-3 ORBIT SCAN: NO Z[1/2] 3x3 PROGRAM BELOW 55 FOR ANY KNOWN SIGNED
  SCHEME (2026-10-20, matmul/f3scan.py)**: Greg asked whether 1/2
  coefficients could beat 55.  A Z[1/2] program reduces mod 3 with the
  same additions (scalings become free signs), so the F_3 orbit minimum
  (GL(3,3)^3 sandwich, 234 monomial cosets per factor, targets up to sign
  + closure bits) bounds every representative reachable by a basis change
  invertible mod 3.  Inputs must be SIGNED: mod-2 classes split into several
  F_3 orbits (the DB's stored i19 member bounds at 56 while the 55 program's
  own point bounds at exactly 55, one coset triple -- the control).  Results:
  all 17,376 DB schemes >= 56 (refined: 56:924 57:2452 58:4293 ...), all
  1,736 new Hell's Bells classes >= 56; Sun's 56 bounds at 56, Perminov's 56
  at 55 (same orbit as the 55), i106's 60 at 56.  So no 1/2-coefficient
  representative of any known scheme goes below 55; only a basis change
  singular mod 3 or an unknown class escapes.  Our own mod-2 corpora are
  unsigned and were not scanned.  Boundary rows are re-scanned at target+1
  (the early-exit lesson, applied before reporting this time).
- **arXiv: 55-ADDITION PAPER ANNOUNCED (2026-10-21 check)**: arXiv:2610.27451
  (listed "Submitted on 20 Oct 2026", the post-moderation resubmission).
  KS-51 (submit/8246158) still on hold, no request.  Zenodo mm55 related
  identifier still to add (v1.1 kit).
- **PLINOPT PR #23 OPENED (2026-10-21 13:10, Greg: "make the PR for our 201
  now")**: https://github.com/jgdumas/plinopt/pull/23 from fork branch
  gsidebottom/plinopt:rational-48-201 (data/4x4x4_48_201_{L,R,P}.{sms,slp},
  title line "# <4x4x4:48|201> by Greg Sidebottom" mirroring Patel's);
  body: counts, checks (SLPchecker, MMchecker, Brent, Patel's checker), the
  Lean proofs (master + permalink e6f8534), provenance and sources.  PR #22
  (the 167) was merged by Dumas on 2026-10-19 (he then compacted its L slp).
- **LEAN, MATRIX FORM (2026-10-21 12:30, Greg's ask)**: proof/Mm/
  Ring_4x4_48_201.lean in the style of Ring51.lean: `rank48_op201_scheme h A B`
  (201 commented lets on Matrix (Fin 4) (Fin 4) R; h = one half) and
  `rank48_op201_scheme_eq_mul (h) (h2 : 2 * h = 1) (A B) : scheme = A * B`,
  proved by ext/fin_cases/simp + one linear_combination per entry whose
  coefficient comes from the RAW h-polynomial expansion (the canonical-form
  coefficients of Correct48_201 fail on the 4 entries whose cone recombines
  halves).  ~90 s, axioms [propext, Classical.choice, Quot.sound].
  Generator matmul/dps48/lean_gen_ring48_201.py (shares lean_gen48_201.py's
  program analysis, which now tracks raw forms too).
- **LEAN CERTIFICATE FOR THE 201 SCHEME (2026-10-21 12:05)**: proof/Mm/
  Correct48_201.lean, `Matmul48_201.correct`: over any commutative ring with
  `2 * h = 1`, the exact programs (201 operation wires, halvings as `u * h`,
  48 products) compute all 16 entries of A*B.  Generated by matmul/dps48/
  lean_gen48_201.py: per-wire canonical-form lemmas (`ring`, or
  `linear_combination e * h2` where halves recombine, e by exact division by
  2h-1), outputs by `linear_combination` of 2h = 1 with generator-computed
  bilinear coefficients; the first attempt (`subst_vars; field_simp; ring`
  on fully inlined goals) timed out.  Compiles in ~15 s, lake build clean,
  no sorry.  Greg's ask: "make a Lean proof that this 201 add scheme is a
  4x4 matrix multiplication to certify it".
- **RANK-48: NEW RECORD 201 = 55 + 57 + 89 (2026-10-21 10:30; Patel's 202)**:
  matmul/dps48/patel/sweep.py with the Rust engine (lns48, matrix-only
  seeds) over the 90 orbit48 pool points: stage A (30 s per side) nine
  points at 202, stage B (120 s) pool_l0.3 cand005 and cand010 at 201 = L 55
  + R 57 + P 89 (P^T 57).  Stored as cand48/p005_201_* (point sms + raw
  programs), p005_201n_* (sign-normalized: zero negations, 201 in Patel's
  model too) and p010_201_*.  Verified: SLPchecker per side on both the
  point's and the normalized matrices, MMchecker x5 (+ x3 at 40 bits), exact
  Brent (slp48check.py), and Patel's own slp.py checker (201, 4096
  identities, DAG).  Stage C (600 s x 2 seeds, top 6): ALL SIX at 201 (L 55
  R 57 P 89, or L 57 R 55 P 89 at pool_l0.5 cand110) -- a plateau.  The
  winners are lambda = 0.3 annealer points (floor 156, 72 non-units); the
  floor-159 sparse68 family tops out at 202.  Follow-ups (11:00-11:40):
  cand005 restarts (12 naive seeds x 180 s): L 55 (11/12), R 57 (12/12),
  P^T 57 (8/12) -> 201 again; orbit climb from cand005 (45 s/side, 36
  proxy-best of 512 neighbours): no neighbour below the incumbent at that
  budget; exactlns (exact windows <= 16, hmax 4) on the 201 programs: 0
  improvements (locally optimal); mod-3 bounds weak (L >= 44, R >= 46, P^T
  >= 40 additions).  Two new lambda = 0.3 annealer pools (400 distinct
  proxy-optimal points each in 90 s; the proxy saturates at 177.6) -> 120
  candidates, sweep 2 running; depth-2 proxy-optimal neighbourhood of
  cand005 (19 points) queued; hot-annealing 20-min runs on cand005's R and
  P^T: both unchanged after 20 min x 2 seeds (330k iterations) -> cand005
  saturated at 201.  SWEEP 2 (120 new lambda = 0.3 points, Rust engine,
  matrix-only seeds; done 12:34): stage A one 201 + 33 at 202; stage C seven
  of the top eight at 201 (L 55 R 57 P 89 or the L/R mirror), none below --
  the proxy-optimal family saturates at 201 at ~15 distinct points over both
  sweeps.  Depth-2 proxy-optimal neighbourhood of cand005 (19 points) being
  swept: stage C 201 at the three Y-shear neighbours, 203 elsewhere (13:25).
  EXPERIMENTS 1+2 (Greg, 13:30, running): orbit48 gained --wl/--wr/--wp/
  --wbal (side weights, L/R balance penalty); pools from four annealer
  variants (balanced and P-weighted from p005, lambda 0.1, balanced from
  Patel's point) plus patel/orbitsample48.py (40 random walks of depth 12,
  not proxy-optimized) -> pool3 (320 points) -> sweep_rust3 (30 s / 120 s /
  600 s x 2).  STAGE A (14:00): new profiles exist and matter -- lambda 0.1
  gives 42/40/38 (floor 152, 47 pts) and 40/40/38 (floor 150, 3 pts); the
  balanced objective gives 44/44/38 from p005 and 42/42/42 from Patel's
  point; P never below floor 38.  Stage-A costs: 40/40/38 ->
  lam01_p005_cand000 at 201 = L 56 + R 56 + P 89 (BALANCED; either side at
  55 would be 200) -- focused restarts.sh running; 42/42/42 -> 203 = L 55 +
  R 55 + P 93 (L+R 110 but P floor 42 -> 93: P costs floor + 51 everywhere);
  42/40/38 -> 204; 44/44/38 -> 204; random non-proxy-optimal samples 212+
  (the proxy-optimal region is the right one).  FINAL (14:52): stage C six
  of eight at 201 (the balanced point 56+56+89 and five 42/44/38 points
  55+57+89), two at 202; the balanced point's P^T (57) and R (56) did not
  move in 20 min x 4 seeds.  Stored: cand48/lam01c0_201_*.  CONCLUSION:
  three structures (55/57/89, 57/55/89, 56/56/89) at exactly 201; P = floor
  + 51 and L + R = 112 across floor-150/156 points; 42/42/42 points give
  L + R = 110 but P 93.  A 200 would need a richer LNS neighbourhood
  (experiment 3: exact sub-problem solves on the value set, P side first),
  a separate project.
- **EXPERIMENT 3 (2026-10-21 15:00-, Greg: "then do experiment 3")**: lns48
  gained --kmax, --metropolis/--maxworse, 512-bit sets and an n48 feature
  build (P searched directly, 48 inputs).  3a kmax 16/24 + 8 orders on
  p005's R and P^T: 57/57 x3 each (baseline 57/57 x3) -- nothing.  3b
  direct P from the 89-op program: 89 x2 (6 it/s).  3e prototype
  patel/mipselect.py (scipy/HiGHS MIP = exact minimum closed subset vs
  greedy reverse deletion on the same dictionary, current + 40 proposals):
  MIP optimal in 4-81 s, optimum 57 in 6/6 trials, greedy 58 in 2/6 -> the
  repair is near-exact; the PROPOSALS are the limit.  3d Metropolis (T 0.7
  and 1.2, best+3, tabu 1024): 57/57 x3 each.  3e in Rust (lns48 --exact:
  HiGHS MIP minimum closed subset in place of greedy deletion, 60 proposals
  per step, 30 s MIP limit, 12 threads x 30 min, ~2000 exact steps): R 57
  x6, P^T 57 x6.  (The Python 300-proposal test was superseded and stopped.)
  CONCLUSION (16:35): the 201 value-set optimum is robust under every
  neighbourhood tried -- wider proposals, exact repair, excursions, direct P
  -- and under every proxy-optimal orbit profile found.  Beating 201 would
  need a genuinely different idea (a lower-bound argument over Z[1/2] to
  show it cannot be done, a different decomposition class, or proposals
  built from the target structure rather than sampled); experiment 3 is
  CLOSED.  Machine was at ~1200% CPU for the final run (Greg's ask).
- **RANK-48: 202 = 55 + 58 + 89 -- TIE WITH PATEL'S RECORD (2026-10-21
  10:07)**: matmul/dps48/patel/restarts.sh (lns48, 12 naive matrix-only
  seeds x 180 s per side): L 55 on all 12 seeds, R 58 on all 12, P^T 57 on
  one seed (others 58-59) -> P 89.  cand48/sparse68_202_* and the
  sign-normalized sparse68_202n_* (signnorm48.py: zero negations, 202 in
  Patel's model too; sms of the flipped matrices included) verified by
  SLPchecker per side, MMchecker x5 (rational mode) and slp48check.py (exact
  Brent).  Follow-ups: P^T 57 -> 56 would give 201 (a 6 x 300 s naive
  campaign gave six 58s; deepening from the 57 program at T 0.35 / tabu 1024
  running); the Rust-engine pool sweep (90 points) and the orbit climb from
  sparse68 (R = 58 is the side 2 above Patel's and has never varied across
  24+ seeds, so a neighbouring point with a cheaper R is the other route).
- **RANK-48: RUST PORT lns48 -> sparse68 at 203 = 55 + 58 + 90 (2026-10-21
  10:15; record 202)**.  Profile of Patel's Python LNS: 72% of a step is
  z3's Python wrapper building ~66 sign-planning problems, and the planner
  only minimizes negations, which PLinOpt does not charge -> `--plinopt-model`
  (greedy signs, no z3) gives 3.3x more iterations and the right objective.
  Then `src/bin/lns48.rs` (Greg: "start the rust port"): fixed-point
  [i64;16] vectors over 1/64, 256-bit catalog/closure bitsets, his six
  proposal families, reverse deletion, descent/plateau/annealing + tabu,
  exact self-verification of every emitted program; ~80 iterations/s per
  thread = 20x the z3-free Python, 70x the original.  Results on sparse68:
  P^T 59 -> 58 (P 90) where Python stalled; L 56 -> 55 from a NAIVE
  matrix-only seed (`--sms`; the chain program is reverse-deleted before
  the search) -- every PLinOpt-seeded run, Python and Rust, had converged
  to 56, and 5-min Rust runs from the 56 program also reach 55: the seed
  decides the basin.  R stays 58 and P^T 58 over 40k iterations and 6+
  seeds (saturated).  Stored: cand48/sparse68_204_* and sparse68_203_*,
  each verified by SLPchecker per side, transpozer for P^T, slp48check.py
  (exact Brent) -- Patel-model count of the 203 triple is 228 (15 output
  negations in L, absorbable into P's input signs; normalize before any
  publication).  Python sweep (patel_phase engine) stopped after stage B:
  best 205 at pool_l0.5_cand115 (L 58, R 56, P 91); L+R = 114 at almost
  every point, P 91-94 decides.  Running 10:00-11:00: restarts.sh on
  sparse68 (12 naive seeds x 180 s per side), then sweep.py with
  LNS_ENGINE=rust LNS_NAIVE=1 over the 90 pool points (30 s / 120 s / 600 s
  x 2).  Next: orbitclimb48.py with the Rust engine from the best point; a
  larger orbit48 pool; cross-phase sign normalization.
- **RANK-48: PATEL'S LNS ON sparse68 -> 205 (2026-10-21 09:00, Greg's go)**:
  his code (CC0) cloned into the session scratchpad, read in full (stdlib +
  z3; `df` is the only subprocess), smoke tests pass, his 203 -> 202
  calibration reproduces in 60 s, and his exact checker independently
  verifies sparse68.  His `rebuild3.py` on sparse68: L 67 -> 56, R 67 ->
  58 (4 workers x 30 min, all converged); his direct-P search stuck at 101,
  but driving his `Search` on P^T (48x16, `matmul/dps48/patel/
  patel_phase.py`) gives P^T 63 -> P 91 via PLinOpt's transpozer (+32).
  TOTAL 205 = 56 + 58 + 91 (PLinOpt count; 213 in his model, which charges
  the 8 output negations), three above the 202 record; stored as
  cand48/sparse68_205_{L,R,P}.slp, verified by SLPchecker, MMchecker and
  the new independent matmul/dps48/slp48check.py (exact Brent over Q, both
  cost models, plus a translator from his `a*(1/2)` syntax, which
  SLPchecker rejects, to `a/2`).  Running: matmul/dps48/patel/sweep.py --
  successive halving (60 s all / 300 s top 20 / 900 s x 2 seeds top 6)
  over the 90 orbit48 pool points, each side seeded by PLinOpt's
  optimizer (P through P^T).  Next: a true-cost hill climb over single
  elementary orbit moves (GL shears, dyadic diagonal scalings, per-product
  (a, b, 1/ab) rescalings) from the best point, proxy-filtered, 60 s per
  side.
- **RANK-48 CAMPAIGN, STEP 3 DONE -- NEGATIVE, AND PATEL'S METHOD FOUND
  (2026-10-21 08:00)**: exact window LNS (matmul/dps48/qexact.py +
  exactlns.py; windows of 6-16 consecutive lines, independent local basis
  with dependent inputs as free signals, per-window helper budget,
  mirabelle-style pair neighbourhoods `--mode pairs`, plateau moves
  `--plateau p` with randomized exact search) finds 0 improvements on
  Patel's L (56), R, P (90) and on sparse68's R (67), P (101); on
  sparse68's L the hmax-4 run gains 3 (70 -> 67 at W=16, stored as
  cand48/sparse68_L.slp; total 235); a diagnostic proves the other consecutive
  windows (W=16) locally optimal with <= 2 helpers each.  So most of the
  slack is GLOBAL (which signals are computed), not local (how a window
  computes them).  Patel's repository
  (github.com/rp440/matmul-4x4-48-202, created Oct 10, `search/` pushed
  Oct 13, code CC0) documents exactly that kind of search: a program is
  identified with its SET OF SIGNAL VECTORS (cost = |set| - inputs + sign
  fixes); each LNS step proposes 1-8 new vectors from six families
  (target residuals t-v, coordinated residual packages, sparse pivots,
  internal residuals, dyadic half/double, broad random combinations),
  adds them to the dictionary, then REVERSE-DELETES removable vectors in
  random order while the set stays closed under one-gate productions
  (x = u +- v, 2u, u/2, proportional rescalings), keeping the cheapest
  state; accepts descent, PLATEAU (equal cost, not in a 256-1024 tabu
  list) and best+1 annealing moves (T = 0.2-0.35); a z3 planner assigns
  signs (negations cost 1 in his model).  Driver: orbit moves (tau, scale
  product k by (a,b) in {+-1,+-2,+-1/2}, elementary shears c in {+-1,
  +-2, +-1/2}) to depth 4 with successive halving (60 s / 300 s / 1200 s
  per phase per seed), 8 processes.  His path: PLinOpt 204 -> scale
  product 20 by (1,-1) + shear Y = I + E_12 -> 203 -> re-optimize L
  (57 -> 56, seed 1803, 60 s) -> 202 = 56 + 56 + 90.  Our PLinOpt
  pipeline reaches only 253 on his point, so his LNS is worth ~50 ops
  there; sparse68 stands at 238 under our pipeline.  NEXT (Greg's call):
  run his rebuild3.py on sparse68's three phases (z3 4.16 is installed
  for Homebrew python3.14), re-verify any result with OUR checkers, and
  if it pays, port the value-set LNS into matmul/dps48 and feed it the
  orbit48 sparse points.  Runs still finishing: exactlns sparse_L2,
  patel_P2, sparse_P2 (2 h caps, expected 0).
- **RANK-48 CAMPAIGN, STEP 2 DONE (2026-10-21 04:20)**: orbit annealing
  (matmul/dps48/orbit48.py, GL(4,Z[1/2])^3, floor + sparsity penalty)
  finds three profiles: Patel's point (floor 150, 104 non-units), the
  DPSST26 canonical profile (146, 38/38/38, 136 non-units) and SPARSE
  points (156-159, 68-72 non-units).  Under every measure the sparse
  points lead: quick optimizer 263 vs 297 (Patel) / 307 (DPSST26);
  Martensson greedy potential 250 vs 278 / 292; pair-level refinement
  (prune_loop.py) 238 = 70+67+101 vs Patel's own point 253 = 68+74+111
  (stored 202).  Saved: matmul/dps48/cand48/sparse68 (MMchecker/SLPchecker
  verified).  The HEAVY STAGE that produced the stored programs is NOT:
  random restarts (5 seeds -> 67-72 on L), triples (71 -> 67 fixed point),
  chartreuse (nothing), long random walks (77 at 10k loops), nullspace
  (81), Martensson brute force (infeasible), PLinOpt -E exhaustive greedy
  (2 h, no program).  Open: Patel's/DPSST26's own method (unknown).
  STEP 3 DESIGN (pending Greg's go): exact sub-program solver over Q --
  for each sub-program that mirabelle would re-optimize (its targets as
  Z[1/2]-vectors over its inputs), iterative deepening on helper count
  with the closure rule generalized to scalars {+-1, +-1/2, +-2}
  (target free if +-a +-b or c*a of available signals), verified splice
  via prune_loop.py; apply to sparse68 first (largest expected payoff),
  then to Patel's point.  Estimate 2-3 days; success = any total < 202.
- **RANK-48 RECORD CAMPAIGN, STEP 1 DONE (2026-10-20 evening)**: target
  = Patel's 202 (PLinOpt data; DPSST26 paper 204).  Base optimizer gives
  78-81 adds on the 202 L side vs stored 54+2: the published counts come
  from PLinOpt's refinement stack (mirabelle/prune sub-program
  re-optimization; needs bash 5.3 + GNU grep/sed/coreutils, installed via
  Homebrew; run dir in the session scratchpad plinopt-run/).  At the 202
  point: pair sweeps L/R/P and triple sweeps L (10,192) / R (8,112): ZERO
  improvements -> no cheap slack.  Fresh-start calibration
  (matmul/dps48/prune_loop.py splices verified improvements, toposort,
  SLPchecker-checked): 87 -> 71 ops by pairs (fixed point, 10 rounds),
  triple continuation running.  Next: step 2 (GL(4,Z) orbit annealing on
  cheap floors) and/or step 3 (exact sub-program solver over Q).
- **RANK-48 (rings with 1/2) MOD-3 POINT BOUNDS (2026-10-20,
  matmul/dps48/f3point48.py)**: at PLinOpt's 202 representative (L 54+2,
  R 54+2, P 90 ops) the F_3 bounds are L >= 42, R >= 42, Pt >= 40 (+32):
  156 vs 198 additions; the 204: 152 vs 200.  Sides sit 12-18 helpers
  above their floors, so closure-level bounds cannot decide slack; an
  exhaustive F_3 orbit scan is infeasible (63,180 cosets per factor).
  Improving 202 needs search over Q (heuristic + small exact), not bounds.
- **ALL THREE RANK-47 CLASSES BOUNDED (2026-10-19 23:10)**: whole-orbit
  lower bounds by lbclass.sh (pre-raise + climb): KM 163 (6.6 h for the
  last step), AlphaTensor 162 (163 step hit its 3.5 h budget, 35 triples
  open), published 160 (161 step: one triple open = the published scheme
  itself, output side Pt (34 targets, BP 49) undecided at level 7 within
  1 h; its L and R sides settled EXACTLY at 44 (6 helpers refuted, 7
  found) -> the paper's open question 'does L admit 43' is answered NO;
  Pt >= 41, so the published scheme costs 160..168).  xor47's parallel exact search now splits two helpers deep
  (balanced; same verdicts on the benchmarks).  Paper: Table 4 gains an
  "orbit >=" column; whole-orbit paragraph covers all three classes.
- **HELL'S BELLS 3x3 DATASET SWEPT (2026-10-19): no improvement.**
  Martensson et al., ePrint 2026/1688, 15,316 rank-23 ternary schemes
  (their best 59; no local search/strong reduction applied).  All pass
  integer Brent.  8,977 equivalent to HKS DB schemes (997 classes; all
  480 floor-47 schemes are DB classes), 6,339 NEW in 1,736 classes
  (floor2 48:11 49:63 50:178 51:312 ...).  Basis change: exact fbmin
  leg screen of the 564 new classes with floor <= 51 -> all ruled out
  for 51 (375 s; control: our 51 class -> TIE-51, legs 12/13/12).
  Flat: new 3x3 whole-orbit bound (hbflat.py: distinct non-unit rows +
  closure bit per leg, LEFT cosets of the permutation matrices, 28 per
  factor, min-plus over 28^3) -> 0 of 1,736 classes can reach 55 at all
  (CORRECTED 2026-10-20: the first run reported "35 classes at exactly
  55" -- an early exit returned the target-count bound without the
  closure bits; refined, those 35 are 57 (13) and 58 (22)); control: our
  55 class bounds at exactly 55.  matmul/hb/README.md.
- **★ S-P 51 KERNEL CLASS-OPTIMAL, MACHINE-CHECKED (2026-10-17)**:
  proof/Mm/SP51Optimal.lean. `kernel_optimal_for_class`: for all
  invertible linear eA eB eC, chains (from ANY nine starting vectors,
  sum-or-difference steps) listing S-P's legs (rows of U, V, columns of
  W mod 2; d = 20 each) give 51 <= nA + nB + (nC + 14), and 13/12/12
  are achieved from a basis; `kernel_optimal_over_int` for integer
  programs via mod-2 reduction. Proof is NOT the fbmin tier search: a
  sum-triple count -- each produced nonzero vector uses a distinct
  triple {a, b, a+b} of listed vectors, so #listed <= 9 + #triples; the
  legs have only 9, 9, 10 triples (floor needs 11). Leg A at 12 adds:
  the one extra vector h needs 3 new triples; only 5 h qualify, each
  with a 2-core (family covering its members twice) -> one triple
  wasted. Kernel `decide` only, ~4 min, axioms standard three. Data:
  matmul/gen_sp51_optimal_data.py. (The same counting may give short
  proofs for other legs: sparse triple structure is common.)
- **PROPOSE-AND-BLOCK (CEGAR) FOR THE CYCLIC 50 (2026-10-16 night,
  f56d622)**: src/bin/symcegar.rs (incremental CaDiCaL server: quotient
  CNF + indicators y_v + counter sum y_v <= 21 + optional relabeling lex
  + budgeted solves) and matmul/symcegar.py (workers: propose, re-verify
  Brent, fbmin decides A-leg <= 12, else shrink to certified cores and
  block each core's 336 images under X -> P X P^-1 and transposition;
  cores shared via cores.txt). Sound: leg cost monotone under inclusion,
  invariant under invertible linear maps; lex removes only relabelings.
  Gates passed: encoding (179/179 canonical census schemes accepted,
  d=22 rejected, non-canonical relabelings rejected, blocks exact); SAT
  side (L=13 finds exact leg 13 on its 3rd proposal); UNSAT side (pinned
  3-free: UNSAT at 12, found at 13). Findings: the census CNF's
  "satsuma" breaking was really unit propagation + 17 binaries; the 170
  census schemes are only 9 A-row-set classes (5 at d=21, 3 at d=22,
  1 at d=20); lex makes the UNSAT side tractable (pinned 4-free: 29 s
  vs >13 min) but it still grows steeply (5-free lex >19 min); lex slows
  proposals (>14 min vs 30-120 s). Production run:
  matmul/external/cyclic/cegar12/ (8 workers: 3 lex, 5 no-lex; 3-day
  cap). Census paused (152 archived). Endgame fallback if the final
  UNSAT stalls: cube on the fixed pair {A21, A22} (639 orbits under the
  336 maps), each cube pinned + lex + all cores.
  Status 23:00: after seeding all 9 census classes (244 cores, 65,016
  blocks with images), 8 workers x 30+ min found NO new scheme and no
  UNSAT -- the census classes may be all of them; the proof is the hard
  part. Cube probes (2 cubes, all cores) > 15 min each. Now running
  both: monolithic (w00 lex + w03-w07 no-lex) and the cube driver
  (e7ec556; w10-w13, cube_reps.txt, cubes_done.txt). Census coincidence
  pattern: the repeated A-blocks always sit in two different orbits,
  never within an orbit or on a fixed product (a further split handle).
  2026-10-17 morning: cube driver stopped at 0/639 (its first 4 cubes
  unresolved after 8.5 h). Production: 11+ h, 5 discovery workers found
  NO new scheme after the census classes were blocked (before: one per
  1-6 min). FINER-SPLIT PROBE (99c01ca, pieces mode): every census
  d=21 class has one orbit whose two blocks equal blocks of two other
  orbits (d=20: a star, one orbit's three blocks matched to three
  orbits); normalized to A0 = A3 = v, A1 = A6 (pos 2 -> 1 by
  transposition), v over the 13 conjugation classes, lex on orbits 3-6
  + fixed, all 244 cores: gate OK (census schemes in normal form valid
  and accepted), but every piece hit the 15-min cap with no verdict and
  no scheme. CryptoMiniSat with native XOR Brent constraints: small
  pinned UNSAT in 44 s (CaDiCaL-like) but no scheme in 10 min on the
  unblocked problem (CaDiCaL: 30-120 s) -- no lever. VERDICT: a proof of
  "no cyclic 50" is out of reach for SAT at this scale; the result
  stands as strong evidence (9 classes, all >= 53; nothing else found in
  11+ h of blocked search).
- **★ FLAT-55 RECORD UNIQUE TO ITS CLASS ACROSS THE DB (2026-10-16,
  b86a1a4)**: new floors --exact-total (exact transposed C table,
  min-plus over 168^3 sandwiches) gated on the record class (=55).
  S-P's class flat min 56 => their one-shot 56 class-optimal
  (7120608). All 616 fat-frontier schemes (cfloor regenerated, exact
  July match): one 55 (record class), rest >= 56; with the July
  slim-sides exhaustive => uniqueness DB-wide. Closes the July
  paper's open item. Six classes at 56 (S-P's among them).
  Basis-change bounds corrected (3b46f4a/dd43672): per
  representative; ours [7,11] for our rep, >= 6 class-wide.
- **FLIP-ADJACENCY HUNT LIVE (2026-10-15, commits 8054e9a+ad520fc)**:
  flipmint.py = the mint funnel over Kauers-Moosbauer flips (the S-P
  move set) with the widened 50-host screen; generator ported to Rust
  (src/flip.rs walk_campaign + flip --walk): **135x measured** (135
  vs 1 new distinct schemes at equal 2-min single-core budget, same
  55 seeds). Running 8 walk + 8 eval threads; mint demoted to a
  3-thread lottery; 01012 lift at 3 threads. Greg's process question
  also flushed a 27 h runaway heredoc (the string-bug novel-52 job);
  killed, core reclaimed.
  walk-00123 class ring-valid at 52 (model 3 of 32 orbits);
  **free-mode conversions EXACT: 4+3+3 = 10, one-shot 62** (free beat
  exact on B, 3 vs 4; C cleared in 40 s once free-d=20 applied — the
  exact-mode d=22 block was two sign-paired rows). walk-01852 class
  ring-valid at 52 too (model 36 of 62! deepest obstruction streak
  yet), **conversions EXACT 5+4+3 = 12, one-shot 64**; 01012 lift
  still looping. Novel-trio scoreboard COMPLETE
  (2026-10-15): 00123 = 52+10 (one-shot 62, model 3), 01852 = 52+12
  (64, model 36), 01012 = 52+13 (65, model 18; conversions 3+4+6,
  the floor 11-leg forces a 9-target basis). All three ring-valid;
  sign gap model-local at 3/36/18 of 32/62/58 orbits. Ready for the
  paper's next revision with the flip-hunt results.

- **TODO (when cores free): measure leg stabilizers** — for each
  51/52-tier class, compute the column-action stabilizer of each leg's
  target set; if nontrivial, orbit-quotient the subset sweeps in
  fbmin/fbsmin (win = stabilizer order). Full gate discipline per
  [[gate-symmetry-actions-on-the-object]]: assert the action fixes the
  target set and orbit sizes sum to C(d,9) before trusting any
  speedup.

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

- **2026-07-16 — benchntt_metal: GPU column for the transform table.**
  Radix-2 stages as Metal kernels (encoder-per-stage ordering; MSL
  gotcha: `half` reserved). Gated bit-for-bit vs CPU (fwd + roundtrip
  at 2^14/2^18). M4 Pro fwd: 0.17ms @ 2^18 (34×), 3.0ms @ 2^22 (39×),
  44ms @ 2^25 (26×); 2^25 audit ≈ 290 GB/s — the NTT saturates
  bandwidth like the tiles did. Small domains launch-bound (72µs @
  2^14 ≈ encoder overhead — why GPU provers batch small NTTs). Paper:
  Appendix B table now 5 columns + GPU prose. The Appendix B/C
  measurement program is complete across fields (BN254/G/BB), stacks
  (Groth16/AIR), and substrates (CPU/NEON/GPU).

- **2026-07-16 — zkML paper consolidation pass.** The abstract now owns
  the measured story (284 record; 17.6× density tax + AIR erasure;
  field- and substrate-dependent crossovers; NTT pricing incl. GPU;
  the substrate law and its convergence on rows-as-currency); header
  carries first-version/revised dates; Appendix C retitled "…on real
  proving stacks and real machines" with an arc-in-one-line intro
  replacing the stale "two headlines"; §7 Program item 4 marked
  largely-done (Lean gadget templates still open; memory-mediated
  precompile chip named as next); §8 Reproduction now lists the whole
  gated measurement suite. Meanwhile: rank-47 hunts (G 5T + BB 4T,
  12 h, pursue10) and the 1500-rep reopt storm on accurate running;
  bpcse R-lane misclassification corrected → task #29 (x8-space
  emission mismatch, to be diagnosed properly).

- **2026-07-17 — mul-schedule AIR (task #30): the row lever measured;
  md/tex divergence caught and repaired.** One parametric 67-col AIR,
  one row per multiplication, scheme wiring in preprocessed columns
  (setup_preprocessed/prove_with_preprocessed; selector products
  precomputed to hold degree ≤ 3; Plonky3 note: extra bounds on the
  Air impl where-clause; periodic columns rejected — 48 ∤ 2^k).
  Naive = 64-row / rank-48 = 48-row schedules of the SAME AIR; host
  trace gen Brent-gates the 284 tables per tile. Verdict at equal
  trace height: **1.337–1.340× tiles/s (theory 1.333×)** — first
  measured prover-side win for rank-48; endpoints now bracket
  deployment (flat-tile parity ↔ full 4/3 when materialized).
  Paper: row-lever paragraph + thesis-in-one-sentence. ALSO: audit
  found the tex had silently missed the earlier density-erasure
  paragraph ("tex updated" print trusted without content
  verification) — repaired, md/tex grep-balanced. Lesson: verify
  mirrored-content presence after each patch, not just script exit.

- **2026-07-17 — exact window resynthesis (task #31): the 284 is locally
  unimprovable at width 12.** New search family: windows.py extracts
  every closed sub-DAG window (≤12 ops, ≤8 in, ≤5 out) from the
  accurate L/R/P programs; exactw.rs answers each exactly
  (branch-and-bound, dyadic menu ±1/±2/±4, ±2^e output matches,
  span/proportionality LBs, caps). First sweep produced 28 phantom
  improvements — traced via checker-reject → Q-evaluator → parser
  mangling PLinOpt's parenthesized-group syntax ((y+z)/2 → invented
  input "2"); parser swapped for shiftmin's group-aware one, phantom
  cluster explained (group-heavy R region). Corrected sweep over 958
  instances + 300 s deep pass on capped windows: **876 proven exactly
  tight, 0 improvements, 82 undecided** — a local-optimality
  certificate strictly stronger than the fixed-point evidence.
  Paper's adds-record passage updated. Beating 284 now requires
  either wider windows (≥13 ops — combinatorially steep), a richer
  coefficient menu, or global restructuring (new decompositions).

- **2026-08-10 — memchip/tilechip (task #32 COMPLETE): sound memory
  argument built from primitives; dilution measured on prediction.**
  Phase 1: uni-stark prover/verifier forked into benchair (compiles
  against public re-exports, zero vendoring), cross-gated behavior-
  identical. Phase 2: the two-stage round — challenges sampled AFTER
  the main commit, perm columns committed second, folded into the
  same quotient/opening; TwoStageBuilder trait (local; chosen over
  p3-air's PermutationAirBuilder for packed-folder friction) with
  prover/verifier/symbolic impls, degree-faithful; LogUp skeleton
  gate + forged-inverse rejection. Phase 3+4: TileChipAir — compute
  band (mul-schedule, one preprocessed one-hot memory op per row:
  32R+16W/tile) + 48-row memory band; last-row LogUp acc==0 IS
  memory consistency; 10 gates green incl. all four forgery classes.
  Measured: rank48/naive 1.176×@2^14, 1.163×@2^16 on the 112/96 =
  1.167× row prediction. Deployment bracket complete: parity (free
  gate) / 1.17× (sound memory) / 1.34× (replicated ceiling) /
  drowned (op-per-row). Paper: 'The memory argument, closed'
  paragraph (md+tex balanced — md anchor wrap caught by the
  post-patch grep balance this time). Program status: the zkML
  measurement arc is COMPLETE end to end.

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
