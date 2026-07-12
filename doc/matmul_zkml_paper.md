# Bilinear Rank as Proof Cost: Fast Matrix-Multiplication Schemes and Field-Specific Flip Search for zkML

*Greg Sidebottom*

*Research note — logic repo (https://github.com/gsidebottom/logic),
matmul track, 2026-07-11. Companion to the 3×3 additive-complexity
paper (`doc/matmul_adds_paper.md`, artifacts DOI
10.5281/zenodo.21240904), the rank-48 rigidity paper
(`doc/matmul_rigid48_paper.md`), and the flower note
(`doc/matmul_flower_paper.md`). The engine described in §5 is
`src/bin/flip23p.rs` in this repository.*

## Abstract

Zero-knowledge machine learning (zkML) — proving that a neural-network
inference was computed correctly without re-executing or revealing it —
is bottlenecked by the prover, whose work in circuit-based proof
systems is counted in **multiplication constraints**: additions and
constant-coefficient linear combinations are free. This is the exact
inversion of the hardware cost model that keeps fast matrix
multiplication out of GPUs, and it makes **bilinear rank** — the number
of multiplications in a Strassen-like scheme — the direct cost driver
for matrix multiplications between witness values (private weights;
attention). Three consequences. (1) Known schemes already pay:
recursive rank-48 4×4 blocking proves a 768×768 witness×witness
product with ≈4× fewer constraints than the naive circuit, penalty-free
because the schemes' additions cost nothing. (2) Coefficient
obstructions vanish: schemes over ℚ with dyadic (or any rational)
coefficients are exact over a prime field, and numerical stability is
not a concept. (3) Most interestingly, **rank is field-dependent** —
rank 47 for 4×4 exists modulo 2 with no characteristic-0 equivalent
known — and zkML fixes a short list of concrete fields (Goldilocks,
BabyBear, M31, the BN254/BLS12-381 scalar fields) over which nobody
has searched. We port our rational flip-graph engine to 𝔽_p
(`flip23p`, Goldilocks first): over a prime field the engine is
strictly stronger than its ℚ parent — no coefficient growth, no
magnitude caps, and every coincidence-solving λ is admissible, so the
coplanarity structure that rationality left mostly unusable becomes
fully spendable. A verified rank-22 3×3 or rank-47 4×4 over a proof
field would be a shippable constraint-count reduction with no analog
in the characteristic-0 literature. We state the cost model precisely,
including the honest carve-outs (sumcheck/GKR provers multiply
matrices in ~n² prover work and do not care about rank; public-weight
linear layers cost no constraints), inventory which of our existing
artifacts transfer, and report the port's first measurements.

## 1. zkML in one page

A **zero-knowledge proof** (ZKP) lets a prover convince a verifier
that a statement holds — here, "this output is what model *M* computes
on input *x*" — without the verifier re-executing the computation, and
optionally without revealing *x* or *M*. Two families dominate.
**SNARKs** (succinct non-interactive arguments of knowledge; Groth16
[6], PLONK [5]) give constant-or-polylog proof sizes over
elliptic-curve-pairing fields such as the BN254 and BLS12-381 scalar
fields (~254/255-bit primes). **STARKs** [2] replace pairings with
hashes, gain transparency and plausible post-quantum security, and
run over small "FFT-friendly" primes chosen for fast NTTs — Goldilocks
p = 2⁶⁴ − 2³² + 1 (Plonky2 [12]), BabyBear p = 2³¹ − 2²⁷ + 1 (RISC
Zero [13]), and M31 = 2³¹ − 1 (Circle STARKs [8]).

The asymmetry that defines the field: verification is cheap, **proving
is 10³–10⁶× the native computation**, all of it exact arithmetic in
the proof field. zkML applications — proving a proprietary model was
faithfully executed (model privacy), proving an inference inside a
blockchain rollup, auditable AI where the checker is cheap — inherit
that overhead on every multiply of every layer. Making matrix
multiplication cheap *inside a proof* is therefore a different
optimization problem from making it fast on silicon, with a different
— in fact opposite — cost model.

## 2. What proving charges

The standard arithmetization, **R1CS** (rank-1 constraint systems, as
in Groth16 [6]), expresses a computation as constraints of the form

```
( Σ aᵢ·wᵢ ) × ( Σ bᵢ·wᵢ ) = ( Σ cᵢ·wᵢ )
```

over the proof field, where *w* is the witness vector and the aᵢ, bᵢ,
cᵢ are **constants**. Each constraint carries exactly one
multiplication of witness values; the linear combinations inside the
parentheses — additions, subtractions, scalings by arbitrary field
constants — are free: they are folded into the constraint's constant
vectors and cost the prover nothing. PLONK-family systems [5] charge
per gate/row with the same shape (custom gates and recent lookup
arguments shift constants around but preserve the headline:
**bilinear multiplications of witnesses are the metered resource**).

For an n×n matrix product C = A·B where both A and B are witnesses,
each output entry C_ij = Σ_k A_ik·B_kj is a sum of n witness×witness
products. A sum of n products is not one rank-1 quadratic form — it
takes n constraints. The naive circuit therefore costs **n³
constraints**. Two situations make both operands witnesses in zkML:
**private weights** (the commercially central case — the model owner
proves inference without revealing the model, so W is witness), and
**attention** (Q·Kᵀ and scores·V multiply two activation matrices —
witness×witness even when all weights are public). Conversely, a
linear layer with *public* weights is a constant linear map and costs
zero multiplication constraints; rank optimization has nothing to
offer there.

**A toy example, 2×2 over 𝔽₁₇.** Take witnesses A = [[1,2],[3,4]]
and B = [[5,6],[7,0]]; then C = A·B ≡ [[2,6],[9,1]] (mod 17). The
naive circuit spends one constraint per product — eight constraints
of the shape u₁ = A₁₁×B₁₁ — and the output sums like
C₁₁ = u₁ + u₂ cost nothing further (they are linear). Strassen's
rank-7 scheme spends **seven**: its first product is the single
constraint

```
( w_A11 + w_A22 ) × ( w_B11 + w_B22 ) = w_P1
```

where all four operand additions sit *inside* the constraint's
linear forms, free. There is exactly **one witness per proof**: a
single vector w over 𝔽₁₇ holding every wire value — a conventional
leading 1 (which lets constraints use constants), the inputs, the
seven products, the outputs. Here it is concretely, all 20
coordinates:

```
w = ( 1 | A: 1,2,3,4 | B: 5,6,7,0 | P: 8,1,6,8,0,5,3 | C: 2,6,9,1 )
```

The subscripted symbols above are coordinates of this one vector,
and each constraint is checked by reading them off: for P₁,
(1 + 4)·(5 + 0) = 25 ≡ 8 ✓, and likewise P₂ = 7·5 = 1,
P₃ = 1·6 = 6, P₄ = 4·2 = 8, P₅ = 3·0 = 0, P₆ = 2·11 = 5,
P₇ = (−2)·7 = 3 (all mod 17). The free output combinations
reproduce C exactly: C₁₁ = P₁+P₄−P₅+P₇ = 19 ≡ 2, C₁₂ = P₃+P₅ = 6,
C₂₁ = P₂+P₄ = 9, C₂₂ = P₁−P₂+P₃+P₆ = 18 ≡ 1. (The prover commits
to w and proves the constraints hold; the verifier never sees w —
that is the "zero-knowledge". Note the naive circuit's witness
carries eight product coordinates to Strassen's seven, so lower rank
also shortens the committed vector.) Seven constraints instead of
eight — 12.5% at one level, compounding to n^2.807 under recursion —
and dyadic coefficients would be equally at home: ½ is just the
constant 9 in 𝔽₁₇ (2·9 = 18 ≡ 1). This is §3's story in miniature;
the rank-23 and rank-48 schemes are the same picture with better
ratios. (Appendix A runs a complete Setup → Prove → Verify on a
two-constraint slice of this example — the whole SNARK pipeline at
hand-checkable scale.)

## 3. Bilinear rank is constraint count

A bilinear scheme of rank r computes the m×m block product with r
products of linear forms: P_t = (Σ α · A-blocks)(Σ β · B-blocks),
then C-blocks = Σ γ·P_t. In R1CS each P_t is exactly one constraint —
the linear forms slide into the constraint's free linear parts — so an
m×m witness×witness block product costs **r constraints instead of
m³**, and recursion compounds it: T(n) = r·T(n/m), i.e.
**n^(log_m r) constraints total, with zero cost for all the
combination additions at every level**. The additions that price fast
schemes out of silicon (§ our hardware discussion) are literally free
here; there is no numerical-stability tax because arithmetic is
exact; and coefficients may be any field constants — our dyadic ½'s
are simply the constant (p+1)/2 mod p.

Idealized constraint counts for a witness×witness product (recursion
to scalar base; real circuits stop at a base tile, which shifts
absolute numbers but not the ordering):

| scheme (exponent) | n = 768 | ratio vs naive | n = 4096 | ratio |
|---|---|---|---|---|
| naive (3.000) | 4.53×10⁸ | 1.0× | 6.87×10¹⁰ | 1.0× |
| 3×3 : 23 (2.854) | 1.72×10⁸ | 2.6× | 2.05×10¹⁰ | 3.4× |
| Strassen 2×2 : 7 (2.807) | 1.26×10⁸ | 3.6× | 1.39×10¹⁰ | 4.9× |
| **4×4 : 48 (2.792)** | 1.14×10⁸ | **4.0×** | 1.23×10¹⁰ | **5.6×** |
| 3×3 : 22 (2.814), *if found* | 1.32×10⁸ | 3.4× | — | — |
| 4×4 : 47 (2.785), *if found* | 1.09×10⁸ | 4.2× | — | — |

Two readings. First, **the wins in the top half are available today**:
the rank-48 scheme [3, 10] with dyadic coefficients drops into any
R1CS/PLONK matmul gadget as-is (our repository carries the verified
scheme and its minimized linear networks). Second, the *marginal* rows
show why new records matter here more than in silicon: each rank step
is a few percent per recursion level, compounding — and unlike
hardware, nothing eats the margin.

## 4. The honest carve-outs

Rank is **not** the lever everywhere, and a fair statement of scope:

- **Sumcheck/GKR provers do matmul in ~n² prover field-ops.** The
  sumcheck protocol has a special-purpose matrix-multiplication
  reduction with prover time near the cost of *evaluating* the
  product (Thaler [4]; GKR [7]); zkCNN [9] and successors build
  dedicated zkML provers on this line. Where such a prover applies,
  bilinear rank is irrelevant. The rank lever applies to the (large)
  circuit-based world: general-purpose SNARK toolchains, zkVMs
  executing matmul as arithmetic, PLONK/R1CS pipelines such as EZKL
  [11], and folding-based IVC (Nova [14]) whose per-step cost is the
  step circuit's constraint count.
- **Public-weight linear layers are free** (constant linear maps);
  rank helps witness×witness products only — private weights and
  attention.
- **Constraint count is not wall-clock.** Prover time also includes
  commitments (MSMs/hashing) whose cost scales with witness length;
  fewer constraints shrink that too, but constants differ by system.
- **Nonlinearities dominate some workloads.** ReLU/quantization take
  range checks and lookups; in convolution- or attention-heavy models
  the matmul share is large, in lookup-heavy quantized pipelines less
  so.

## 5. Field-specific rank: the open frontier, and the flip23p engine

Bilinear rank depends on the coefficient field. The emblem:
AlphaTensor's rank-**47** 4×4 scheme exists over 𝔽₂ [3], no
characteristic-0 rank-47 is known, and our companion work proved the
only ℚ-usable rank-48 class *rigid* under a large certified move
system — evidence that characteristic 0 is genuinely constrained in
ways a fixed finite field need not be. zkML nominates a short,
concrete list of fields that matter commercially — Goldilocks,
BabyBear, M31, BN254-Fr, BLS12-381-Fr — and, to our knowledge, **no
rank search has ever been run over any of them**: the flip-graph
literature works over 𝔽₂ (and small extensions) [15], the explicit
records over ℤ/ℚ. A verified 3×3 rank-22 — or 4×4 rank-47 — over
Goldilocks would be a new kind of record with an immediate consumer:
2–4% fewer constraints per recursion level in deployed proof systems,
compounding as in §3's table.

`flip23p` is our rational flip engine (splits, λ-flips, reductions,
canonical gauge, exact Brent verification — the machinery of the
companion papers) re-based onto 𝔽_p, Goldilocks first. Over a prime
field the engine is *strictly stronger* than its ℚ parent:

1. **No coefficient growth.** ℚ-walks need magnitude caps and dyadic
   bookkeeping; field elements don't grow. Every cap in the ℚ engine
   is deleted, not loosened.
2. **Every solved flip is admissible.** Over ℚ, a coincidence
   (f_i + λ·f_j ∝ f_m, the Cramer-solved move that makes flips
   productive) is usable only when λ is dyadic — the filter discarded
   most solutions. Over 𝔽_p every nondegenerate solution is a legal
   move: the coplanarity structure ("H4's raw material" in the flower
   note) becomes fully spendable.
3. **The gauge simplifies.** Canonical form is monic normalization
   (leading coefficient 1, scalars folded into the c-slot);
   proportional ⇔ equal, exactly as before, with none of ℚ's
   content/sign bookkeeping.

First measurements (2026-07-11, all mechanically checkable — §8):
the 55-addition record scheme loads and verifies over Goldilocks
(729 Brent equations mod p); the census gate matches the ℚ engine
exactly (9 shared pairs, weight 177, distinct-rows 40). One honest
surprise: the seed's solved-move silence is *not* the dyadic filter's
fault — even with all field λ available, its 9 shared pairs admit no
coincidence solution; the coplanarity geometry genuinely fails there.
Mobility arrives at once elsewhere: a 25-second smoke storm from the
most mobile census seed executed 1.3M moves with 369K solved flips
and ~10K reductions — a far higher solved-flip fraction than the ℚ
storm ever achieved, the freed λ paying immediately. No sub-23 rank
has appeared in smoke tests (nor was one expected at that effort);
the campaigns are the point.

## 6. What transfers from the existing program

- **Engines and discipline.** flip48/flip23's storm, closure, census,
  novelty and thin-storm machinery ports mechanically (v1 of flip23p
  carries storm/census/closures; the beam-chase and exhaustive
  campaign modes follow). The operational rules hard-won in the
  companion papers — completion logs, full-frontier dumps, control
  baselines, budget caps — apply verbatim.
- **Seeds.** Every scheme we hold is a valid 𝔽_p scheme: the 17,376
  database classes, our 53 lifted classes, the 46 storm-new classes,
  and the 467 mod-2-invisible dyadic ℚ-schemes (denominators are
  field constants). The mobility census that ranked ℚ-seeds re-runs
  unchanged over 𝔽_p.
- **Verified gadgets.** The Lean pipeline that certified the 55-add
  scheme extends naturally: a scheme-to-circuit emitter (circom /
  Halo2 templates for the 23- and 48-multiplication blocks) with a
  machine-checked correctness certificate is a deliverable the
  proof-systems world actually values.
- **What does not transfer:** the additive-complexity results (55
  adds, the no-54 theorem). Additions are free here; that program's
  value stays in classical hardware and in witness-generation speed.

## 7. Program

1. **Goldilocks campaigns** (`flip23p`): storm + closure portfolios
   over the census-ranked seeds; targets, in order of plausibility ×
   value: any new-class harvest over 𝔽_p, rank 22 at 3×3, rank 47 at
   4×4 (the 4×4 port is the same edit at 16 coordinates).
2. **Small-field variants**: BabyBear and M31 (31-bit arithmetic,
   ~4× faster walks), then BN254-Fr for the pairing world.
3. **Rectangular tiles**: transformer shapes want ⟨m,n,k⟩ records
   (⟨3,3,6⟩-style); the engine generalizes as flip48 → flip23 did.
4. **Verified gadget emitter + benchmark note**: constraint-count
   measurements in an EZKL-style stack, naive vs recursive-scheme,
   with Lean-certified gadget templates.

## 8. Reproduction

```bash
cargo build --release --bin flip23p
./target/release/flip23p --census --dir matmul/mm23      # gates
./target/release/flip23p --dir matmul/seeds23/13a5bd4n \
    --seconds 25 --threads 4 --out matmul/found23p       # smoke storm
# any verified rank <= 22 over Goldilocks lands in
# found23p/RECORDP_rank*.txt and is announced loudly
```

## Appendix A. Setup, Prove, Verify — a complete toy proof

This appendix runs the entire SNARK pipeline, Groth16-shaped, on a
two-constraint slice of §2's example, every number over 𝔽₁₇. One
honest simplification, flagged where it occurs: real systems wrap the
values below in elliptic-curve encodings ("in the exponent"), which
is what makes hiding cryptographic; the *arithmetic* — R1CS → QAP →
divisibility check at a secret point — is shown here exactly as real
provers compute it.

**The statement.** For reference, the full toy matrices of §2, whose
entries supply every private value below:

```
A = [ 1 2 ]     B = [ 5 6 ]     C = A·B ≡ [ 2 6 ]   (mod 17)
    [ 3 4 ]         [ 7 0 ]               [ 9 1 ]
```

The prover claims: "I know private values A₁₁, A₂₂, B₁₁, B₁₂, B₂₂
(here 1, 4, 5, 6, 0 — the marked entries of A and B) such that
P₁ = (A₁₁+A₂₂)(B₁₁+B₂₂) = 8 and P₃ = A₁₁(B₁₂−B₂₂) = 6." The claimed
products (8, 6) are **public**; the five inputs stay private. The witness (public part first):

```
w = ( 1, P₁=8, P₃=6 | A₁₁=1, A₂₂=4, B₁₁=5, B₁₂=6, B₂₂=0 )
```

and the two R1CS constraints (check: 5·5 = 25 ≡ 8 ✓, 1·6 = 6 ✓):

```
c1:  ( w_A11 + w_A22 ) × ( w_B11 + w_B22 ) = w_P1
c2:  ( w_A11 )         × ( w_B12 − w_B22 ) = w_P3
```

**Step 0 — constraints become one polynomial identity (the QAP).**
QAP stands for **Quadratic Arithmetic Program** [19] — the standard
compilation of an R1CS into a single polynomial divisibility test,
so that "all constraints hold" can later be checked at *one point*
instead of once per constraint. Three sub-steps.

*(a) Read off each constraint's coefficients.* A witness
**coordinate** is one entry of the vector w (such as w_A11); each
constraint assigns every coordinate three constant **coefficients**
— its multiplier in the left factor, in the right factor, and on
the output side. Our two constraints, written out in full:

```
c₁:  left  = 1·w_A11 + 1·w_A22     (every unlisted coordinate: 0)
     right = 1·w_B11 + 1·w_B22
     out   = 1·w_P1
c₂:  left  = 1·w_A11
     right = 1·w_B12 + (−1)·w_B22
     out   = 1·w_P3
```

*(b) Build the Lagrange interpolation basis.* Assign constraint c_j
to the evaluation point x = j. The **Lagrange basis polynomial**
L_j(x) is the unique lowest-degree polynomial equal to 1 at its own
point and 0 at every other; the general formula is
L_j(x) = Π_{k≠j} (x − k)/(j − k), which for our two points {1, 2}
gives

```
L₁(x) = (x−2)/(1−2) = 2 − x        L₁(1) = 1,  L₁(2) = 0
L₂(x) = (x−1)/(2−1) = x − 1        L₂(1) = 0,  L₂(2) = 1
```

(over 𝔽₁₇ the division by 1−2 = −1 is just multiplication by 16 —
every nonzero denominator is invertible in a field). These are
building blocks: the polynomial taking values (v₁, v₂) at points
(1, 2) is exactly v₁·L₁ + v₂·L₂.

*(c) Interpolate each coordinate's coefficients.* For coordinate k,
collect its left-factor coefficients across the constraints as a
value list (value in c₁, value in c₂) and set
A_k(x) = (coeff in c₁)·L₁(x) + (coeff in c₂)·L₂(x); likewise B_k(x)
from the right-factor coefficients and C_k(x) from the output
coefficients. Two worked rows: A₂₂ has left-coefficients (1, 0), so
its A-poly is 1·L₁ + 0·L₂ = 2−x; B₂₂ has right-coefficients
(1, −1), so its B-poly is L₁ − L₂ = (2−x) − (x−1) = 3−2x. The full
table:

| coordinate | in A-side of | A-poly | in B-side of | B-poly | in C-side of | C-poly |
|---|---|---|---|---|---|---|
| A₁₁ | c1, c2 | 1 | — | 0 | — | 0 |
| A₂₂ | c1 | 2−x | — | 0 | — | 0 |
| B₁₁ | — | 0 | c1 | 2−x | — | 0 |
| B₁₂ | — | 0 | c2 | x−1 | — | 0 |
| B₂₂ | — | 0 | c1 (+), c2 (−) | 3−2x | — | 0 |
| P₁ | — | 0 | — | 0 | c1 | 2−x |
| P₃ | — | 0 | — | 0 | c2 | x−1 |

Now weight each polynomial by its witness value and sum:

```
A(x) = 1·1 + 4·(2−x)            = 9 − 4x
B(x) = 5·(2−x) + 6·(x−1) + 0·(3−2x) = x + 4
C(x) = 8·(2−x) + 6·(x−1)        = 10 − 2x
```

Sanity: at x=1, A·B = 5·5 = 25 ≡ 8 = C ✓ (constraint c1); at x=2,
A·B = 1·6 = 6 = C ✓ (c2). **Both constraints hold ⟺ A(x)·B(x) −
C(x) vanishes at x = 1 and x = 2 ⟺ it is divisible by
Z(x) = (x−1)(x−2).** Indeed, over 𝔽₁₇:

```
P(x) = A(x)·B(x) − C(x) = −4x² − 5x + 26  ≡  13x² + 12x + 9
Z(x) = x² − 3x + 2       ≡  x² + 14x + 2
H(x) = P(x) / Z(x)       =  13      (exact division, remainder 0)
```

**Where Z comes from.** Z is the **vanishing polynomial** of the
constraint points. Constraint c_j holds exactly when
P(j) = A(j)·B(j) − C(j) = 0 — that is, when (x − j) divides P. Both
constraints hold exactly when (x−1) and (x−2) *both* divide P,
i.e. when their product Z(x) = (x−1)(x−2) = x² − 3x + 2 does. (With
m constraints, Z = (x−1)(x−2)···(x−m): one root per constraint —
"P vanishes wherever a constraint lives.")

**How H = 13 was computed.** Ordinary polynomial division over 𝔽₁₇
— and in this tiny case it collapses to one step: P and Z both have
degree 2, so H must be the constant (leading coefficient of P) ÷
(leading coefficient of Z) = 13 ÷ 1 = 13, and exactness is checked
by one multiplication:

```
13·Z = 13x² + 13·(−3)·x + 13·2 = 13x² − 39x + 26
     ≡ 13x² + 12x + 9   (mod 17)     = P exactly — remainder 0 ✓
```

(−39 ≡ 12 and 26 ≡ 9 mod 17.) The exactness is not an algebraic
accident; it is the entire content of the proof: **division comes
out clean precisely because the witness satisfies both
constraints**. Tamper with the claim — say the prover asserts
P₁ = 9 instead of 8 — and C(x) becomes 9(2−x) + 6(x−1), so
P(1) = 25 − 9 = 16 ≠ 0: now (x−1) no longer divides P, no valid H
exists at all, and the cheater's only remaining hope is faking the
divisibility check at the one hidden point τ — which is exactly
what Step 3's Schwartz–Zippel argument makes overwhelmingly
unlikely.

The prover's secret knowledge is now compressed into: "I can exhibit
polynomials A, B, C (correctly witness-weighted) and a quotient H
with A·B − C = H·Z."

**Step 1 — Setup (the trusted ceremony).** Sample a secret point,
say **τ = 5** — the "toxic waste" — and publish the *powers of τ and
the QAP polynomials evaluated at τ*, each wrapped in an encoding
that allows additions and scalings but hides the value (in real
systems, elliptic-curve points g^(τ^i); in this toy we will write
the bare numbers and mark where hiding matters). Then **destroy τ**.
Anyone who keeps τ can forge proofs — hence "trusted setup," the
multi-party ceremonies around Groth16, and the transparent (no-τ)
alternatives like STARKs.

For our toy, the published material (the **common reference
string**, CRS) is *witness-independent* — one ceremony serves every
future proof of this circuit — and consists of the encoded
evaluations at τ = 5 of each *coordinate* polynomial from Step 0's
table, plus Z(5) and encodings of the powers of τ that H may need
(here just τ⁰, since our H has degree 0). Spelled out, using the
table's polynomials:

```
A-side:  A_A11(5) = 1          A_A22(5) = 2−5 ≡ 14
B-side:  B_B11(5) = 2−5 ≡ 14   B_B12(5) = 5−1 = 4   B_B22(5) = 3−10 ≡ 10
C-side:  C_P1(5)  = 2−5 ≡ 14   C_P3(5)  = 5−1 = 4
plus:    Z(5) = 4·3 = 12       enc(τ⁰) = enc(1), …
```

(every unlisted coordinate's polynomial is identically 0 and
contributes nothing). Note what is **not** published: anything
witness-dependent — A(x), B(x), C(x), P(x), H(x) belong to the
prover, not the setup.

**Step 2 — Prove.** The prover, holding w, computes the *encoded*
evaluations at τ — crucially, each is a **linear combination** of
published encodings with witness coefficients (this is why R1CS's
free-linear-combination structure is the whole design):

```
A(5) = w_A11·A_A11(5) + w_A22·A_A22(5) = 1·1 + 4·14 = 57 ≡ 6
B(5) = 5·14 + 6·4 + 0·10               = 94       ≡ 9
C(5) = 8·14 + 6·4                      = 136      ≡ 0
H(5) = 13·enc(τ⁰)                      = 13
```

Cross-check against direct evaluation (which only we, the
omniscient narrators, can do): A(x) = 9−4x at 5 gives 9 − 20 ≡ 6 ✓,
B = x+4 gives 9 ✓, C = 10−2x gives 0 ✓ — the same numbers, but the
prover's route touched only published encodings and witness values,
never τ itself.

The proof is π = (enc(A(5)), enc(B(5)), enc(C_priv(5)), enc(H(5)))
— in Groth16, after optimizations, three curve points, ~200 bytes,
*independent of circuit size*. The prover never learns τ; it only
ever combines published encodings.

**Step 3 — Verify.** The verifier reconstructs the *public* part of
C(τ) itself from the claimed outputs (8, 6) and the published
encodings — the prover cannot lie about what P₁, P₃ are claimed to
be — then checks **one multiplicative relation** (in real systems,
one pairing equation; pairings are exactly the tool that multiplies
two hidden values once):

```
A(τ)·B(τ) − C(τ)  =?  H(τ)·Z(τ)
   6 · 9   −  0   =   54 ≡ 3
  13 · 12         =  156 ≡ 3     ✓  accept
```

**Why this convinces (soundness).** A cheating prover with no valid
witness needs A·B − C divisible by Z; the best it can do is fake the
relation *at the single hidden point τ*. Two distinct low-degree
polynomials agree at a random point with probability ≤ deg/|𝔽| —
about 2/17 in the toy (which is why 𝔽₁₇ is a classroom field), about
2⁻²⁵⁰ over a real 254-bit field. Not knowing τ, the prover cannot
aim; that is the Schwartz–Zippel heart of the whole construction.

**Why it reveals nothing (zero-knowledge).** The verifier sees only
encodings — curve points hiding A(τ), B(τ), H(τ) — never the
witness coordinates. (Full Groth16 additionally *randomizes* each
proof: the prover adds masking multiples of Z(x) so that even two
proofs of the same witness look independent; we omit that term for
clarity.)

**And the connection to rank, one last time**: each constraint
became one interpolation point, one row of the QAP tables above, one
share of the prover's work and of the setup's size. Prove a
witness×witness matrix product with a rank-r scheme and this entire
pipeline is r constraints per block instead of m³ — the additions
never appear as constraints at any stage; they live inside the
linear combinations, which the encodings support for free.

## Acknowledgments

This work was carried out in an extended interactive collaboration
with Claude (Anthropic; the Fable 5 and Opus 4.8 models), which
implemented the engines and drafted this text under the author's
direction and review.

## References

1. V. Strassen. *Gaussian elimination is not optimal.* Numer. Math.
   13:354–356, 1969.
2. E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev. *Scalable,
   transparent, and post-quantum secure computational integrity.*
   ePrint 2018/046.
3. A. Fawzi et al. *Discovering faster matrix multiplication
   algorithms with reinforcement learning.* Nature 610:47–53, 2022.
   (AlphaTensor; rank 47 over 𝔽₂.)
4. J. Thaler. *Time-optimal interactive proofs for circuit
   evaluation.* CRYPTO 2013. (Sumcheck matmul in ~n² prover time.)
5. A. Gabizon, Z. Williamson, O. Ciobotaru. *PLONK: Permutations over
   Lagrange-bases for Oecumenical Noninteractive arguments of
   Knowledge.* ePrint 2019/953.
6. J. Groth. *On the size of pairing-based non-interactive
   arguments.* EUROCRYPT 2016.
7. S. Goldwasser, Y. T. Kalai, G. N. Rothblum. *Delegating
   computation: interactive proofs for muggles.* STOC 2008.
8. U. Haböck, D. Levit, S. Papini. *Circle STARKs.* ePrint 2024/278.
   (M31.)
9. T. Liu, X. Xie, Y. Zhang. *zkCNN: Zero-knowledge proofs for
   convolutional neural network predictions and accuracy.* CCS 2021.
10. J.-G. Dumas, C. Pernet, A. Sedoglavic. *A non-commutative
    algorithm for multiplying 4×4 matrices using 48 non-complex
    multiplications.* arXiv:2506.13242. Also: A. Novikov et al.
    *AlphaEvolve.* arXiv:2506.13131.
11. EZKL: `github.com/zkonduit/ezkl` (PLONK-family zkML toolchain).
12. Polygon Zero. *Plonky2: fast recursive arguments with PLONK and
    FRI.* Whitepaper, 2022. (Goldilocks field.)
13. RISC Zero. *zkVM technical documentation*, 2023. (BabyBear.)
14. A. Kothapalli, S. Setty, I. Tzialla. *Nova: recursive
    zero-knowledge arguments from folding schemes.* CRYPTO 2022.
15. M. Kauers, J. Moosbauer. *Flip graphs for matrix multiplication.*
    arXiv:2212.01175.
16. G. Grassi, D. Khovratovich, C. Rechberger, A. Roy,
    M. Schofnegger. *Poseidon: a new hash function for
    zero-knowledge proof systems.* USENIX Security 2021.
17. G. Sidebottom. *A 55-addition rank-23 scheme for 3×3 matrix
    multiplication via exact two-sided minimization.* This
    repository, 2026. Artifacts: DOI 10.5281/zenodo.21240904.
18. G. Sidebottom. *Rigidity of the rank-48 4×4 scheme under solved
    flip moves* and *The Flower.* Companion notes, this repository,
    2026.
19. R. Gennaro, C. Gentry, B. Parno, M. Raykova. *Quadratic span
    programs and succinct NIZKs without PCPs.* EUROCRYPT 2013. (The
    QAP compilation.)
