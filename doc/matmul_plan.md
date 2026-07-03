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

- **R1 — Rust native-ANF SLS engine.** New `src/anf.rs` + bin: Brent
  generator embedded, probSAT-style scoring (cached break counts, adaptive
  noise, restarts), bitset partner tests. Baseline interop: read/write their
  DIMACS + decode their base-var convention (summand-major 27-blocks).
  **Gate: ≥10⁷ flips/s single-core; solve seeded (414-fix) instances ≪1 s;
  solve some pairing+streamliner instances (paper: seconds-minutes for
  yalsat).** Equal-wall-clock A/B vs yalsat on their instances
  ([[compare-search-methods-at-equal-budget]]; yalsat build needs user OK —
  first attempt was permission-blocked).
- **R2 — structure moves.** Native pairing generation (method-1 cores),
  streamliners as constraints/initializers, seeded neighborhood mode, and
  the **tri-linear Gauss closure move** (fix two tensors, exact-solve the
  third via GF(2) elimination; also usable as "repair γ exactly, walk on
  α,β"). **Gate: from-scratch new-scheme pipeline at ≤ minutes/scheme on
  M4 Pro (paper: CPU-hours), schemes verifier-confirmed and
  distinct-after-summand-sort.** Stretch: challenge 1 (pairing, *no*
  streamliners) beyond yalsat's 5/10.
- **R3 — connection-method path-space SLS** (the research question). Local
  search over per-equation satisfaction scenarios on the NNF matrix
  (connections = shared-var conflicts), vs assignment-space SLS at equal
  budget. Honest gate: any slice where it wins; a clean negative is
  publishable insight too.
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
