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
  - Campaign: ~35 CPU-years → **>17,000 inequivalent new 23-schemes** (up
    from 4 known). None compresses to 22.
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
- **Later options**: MCGS/learned policy over restart seeds / move classes
  (ties back to the neural track); UNSAT side (challenge 2) via our proof
  machinery — a *different* project (algebraic/symmetry lower-bound
  reasoning, not enumeration).

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
