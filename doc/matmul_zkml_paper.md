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
Zero [13]), and M31 = 2³¹ − 1 (Circle STARKs [8]). (Appendix B explains the FFT/NTT
layer these fields are engineered for.)

The asymmetry that defines the field: verification is cheap, **proving
is 10³ to 10⁶× the native computation**, all of it exact arithmetic in
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
| 3×3 : 22 (2.814), *if found* | 1.31×10⁸ | 3.4× | 1.46×10¹⁰ | 4.7× |
| 4×4 : 47 (2.777), *if found* | 1.03×10⁸ | 4.4× | 1.08×10¹⁰ | **6.4×** |

**A commutative carve-in.** One refinement the table above does not
yet fold in: bilinear rank assumes non-commuting entries (that is
what makes block recursion valid), but **R1CS witnesses are field
elements and commute** — so at the *base tile* of a recursion the
true cost is the smaller commutative multiplicative complexity.
Rosowski [22] multiplies 3×3 in **21** products over a commutative
ring (vs bilinear 23; Makarov's earlier 22), and in general odd-n
tiles cost n(n²+2n−1)/2: 5×5 in 85 (vs 93), 7×7 in 217 (vs 250).
Blocks do not commute, so interior levels must stay bilinear —
this is strictly a base-tile lever (and 2×2 gains nothing: 7 is
optimal even commutatively) — but any recursion bottoming on 3×3
tiles saves 21/23 ≈ 8.7% of its *entire* constraint count, and the
optimal tile choice is a small dynamic program we leave as a
refinement. Flip-graph search has recently been extended to
commutative schemes [23], so the discovery machinery of §5 has a
commutative analogue if the base-tile hunt ever warrants it.
Quantified against Appendix B.5's bilinear wins: stopping the
rank-48 recursion at an odd tile t and paying Rosowski's R(t)
multiplies the total by R(t)/t^2.792 — 0.977 at t = 3, 0.950 at
t = 5, **0.947 at t = 7** (the optimum) — so today's commutative
ceiling is a ≈5.3% saving, smaller than a rank-47's 13.5% or a
rank-21's 19%, and for the structural reason one should expect: a
bilinear record improves the *exponent* and compounds through
every level, while commutativity improves one *constant* at the
bottom. It stacks multiplicatively with any bilinear win, costs no
new mathematics, and — the pricing surprise — is extremely
sensitive at the smallest tile: each −1 on the 3×3 commutative
count is worth 4.65% of the entire pipeline (3^2.792 is small), so
a 3×3 commutative scheme with 20 products would deliver 7.0% and
with 19 products 11.6% — rank-47-class wins from a search space
minuscule beside the bilinear ones, with known lower bounds
leaving room in the mid-teens. We know of no deployed ZK system
exploiting fast multiplication at all — circuit-based practice
proves matmul naively, and the systems that escape n³ do so by
*verification* (Freivalds-style random projection, the sumcheck
line of §4), not by faster multiplication — so both levers, the
exponent and the tile, are currently unshipped.

Two readings. First, **the wins in the top half are available today**:
the rank-48 scheme [24, 10] with dyadic coefficients drops into any
R1CS/PLONK matmul gadget as-is — and "works over 𝔽_p" is not a
conjecture: our engines load the scheme and verify all 4096 Brent
equations exactly over Goldilocks, BabyBear, and M31 (§5; the
dyadic ½'s are the field constants (p+1)/2 etc.). Only
characteristic 2 excludes it. (Our repository carries the verified
scheme and its minimized linear networks.) Second, the *marginal* rows
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
  One further assumption our ratios inherit: "additions are free"
  holds for the constraint *count*, but deep recursion densifies the
  R1CS rows — each level multiplies the nonzero coefficients in the
  constraints' linear forms, and the prover's linear-algebra phase
  (computing A·w, B·w, C·w and the witness itself) scales with that
  density. This is exactly the lever our companion additions work
  pulls: low-adds schemes (the 55-add 3×3 networks; the DPS 341-op
  rank-48 networks) bound the densification rate, so rank and adds
  are dual levers — rank sets how many constraints, adds set how
  dense they are.
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
2 to 4% fewer constraints per recursion level in deployed proof systems,
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

(Why no A₁₂, A₂₁, B₂₁ here, when §2's full witness carries every
entry? Because this appendix proves only the two-constraint slice:
a witness coordinate earns its place by being *wired into some
constraint*, and c₁, c₂ below never touch those entries. Including
them would just add all-zero rows to the QAP table — their
coefficient polynomials would be identically 0 on all three sides.
In the full 7-constraint Strassen proof all eight inputs appear,
since e.g. M₅ = (A₁₁+A₁₂)B₂₂ wires in A₁₂. Note the contrast:
B₂₂ = 0 *is* present despite its value being zero — membership is
about the circuit's wiring, not the value.)

The two R1CS constraints (check: 5·5 = 25 ≡ 8 ✓, 1·6 = 6 ✓):

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
enc(·) that allows additions and scalings but hides the value —
defined concretely just below. Then **destroy τ**.
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

**What enc(·) is.** Exponentiation in a group where the reverse
direction — recovering the exponent, the *discrete logarithm* — is
computationally infeasible: fix a public generator g and set
enc(v) = gᵛ. Real systems use elliptic-curve groups of size ~2²⁵⁶;
our toy admits an honest miniature. Inside the integers mod 103 (a
prime), the powers of g = 72 form a subgroup of order exactly 17 —
72¹⁷ ≡ 1 (mod 103) and no smaller power is 1 — so exponents live
precisely in our field 𝔽₁₇:

```
enc(v) = 72^v mod 103:
enc(0)=1    enc(1)=72   enc(4)=23   enc(6)=61   enc(9)=81
enc(10)=64  enc(12)=13  enc(13)=9   enc(14)=30
```

What Setup *literally* publishes is this column: enc(1) = 72,
enc(14) = 30, enc(4) = 23, enc(10) = 64 for the coordinate
polynomials, enc(12) = 13 for Z(5) — the raw values in the table
above were narrator's courtesy. (That enc(12) = 13 numerically
equals H's value is pure coincidence of the toy.) Two properties do
all the work:

1. **Hiding.** Recovering v from 72ᵛ mod 103 is the discrete-log
   problem — brute-forceable at order 17 (the toy's one dishonesty:
   only 17 candidates to try) but infeasible at order ~2²⁵⁶. This
   is why the ceremony can publish encodings of powers of τ without
   revealing τ.
2. **Linearity passes through.** enc(a)·enc(b) = g^(a+b) =
   enc(a+b), and enc(v)ᶜ = enc(c·v) for any *known* scalar c. So
   anyone holding encodings can form any known-coefficient linear
   combination of the hidden values — without decoding anything.

What the encoding can *never* do is multiply two hidden values.
That asymmetry is the crypto-layer origin of this paper's entire
cost model: linear operations ride through the encoding for free,
while each hidden×hidden product must be paid for as a constraint —
and the verifier's single pairing (Step 3) grants exactly one such
product, just enough for the final check.

**Step 2 — Prove.** The prover, holding w, computes the *encoded*
evaluations at τ — crucially, each is a **linear combination** of
published encodings with witness coefficients (this is why R1CS's
free-linear-combination structure is the whole design):

```
A(5) = w_A11·A_A11(5) + w_A22·A_A22(5) = 1·1 + 4·14 = 57 ≡ 6
B(5) = 5·14 + 6·4 + 0·10               = 94       ≡ 9
C(5) = 8·14 + 6·4                      = 136      ≡ 0
H(5) = 13·τ⁰   (H is the constant 13)  = 13
```

Cross-check against direct evaluation (which only we, the
omniscient narrators, can do): A(x) = 9−4x at 5 gives 9 − 20 ≡ 6 ✓,
B = x+4 gives 9 ✓, C = 10−2x gives 0 ✓ — the same numbers, but the
prover's route touched only published encodings and witness values,
never τ itself.

In encoded form — which is all a real prover ever holds — the same
combinations run *inside the group*, by property 2:

```
enc(A(5)) = enc(A_A11(5))^w_A11 · enc(A_A22(5))^w_A22
          = 72¹ · 30⁴  =  72 · 8  ≡  61 (mod 103)  = enc(6)  ✓
enc(B(5)) = 30⁵ · 23⁶ · 64⁰  ≡  81   = enc(9)  ✓
enc(C(5)) = 30⁸ · 23⁶        ≡   1   = enc(0)  ✓
enc(H(5)) = enc(τ⁰)¹³ = 72¹³ ≡   9   = enc(13) ✓
```

The transmitted proof is literally those four group elements,
**π = (61, 81, 1, 9)**, and nothing else. (Both C-coordinates here
happen to be public outputs, so the verifier could rebuild
enc(C(5)) itself; in general the proof carries the private part
C_priv.) In Groth16, after optimizations, the proof compresses to
three curve points, ~200 bytes, *independent of circuit size*. The
prover never learns τ; it only ever combines published encodings.

**Step 3 — Verify.** The verifier reconstructs the *public* part of
C(τ) itself from the claimed outputs (8, 6) and the published
encodings — the prover cannot lie about what P₁, P₃ are claimed to
be — then checks **one multiplicative relation**. In real systems
this is one *pairing* equation: a pairing e(·,·) satisfies
e(gᵃ, gᵇ) = e(g,g)^(a·b), multiplying two hidden values exactly
once — the single multiplication the encoding ever grants. Our
mod-103 toy group has no pairing, so here (the toy's one honest
deviation) we decode and check in the clear:

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

## Appendix B. The FFT/NTT layer — how the polynomial pipeline scales

Appendix A ran the whole pipeline at two constraints, where every
polynomial step was hand-arithmetic: interpolate from two points,
one product, one division. A real circuit has *millions* of
constraints, and each of those steps done naively costs O(m²) field
operations. The workhorse that makes them O(m log m) is the fast
Fourier transform run over 𝔽_p — the **NTT** (number-theoretic
transform). This appendix shows it working at toy scale in the same
𝔽₁₇, then gives the production numbers.

**B.1 Where transforms appear.** Four steps of Appendix A become
transform calls at scale:

1. *Interpolation* (Step 0): witness columns → the coefficient
   polynomials A(x), B(x), C(x). One **inverse NTT** each replaces
   the O(m²) Lagrange formulas.
2. *Products* such as A(x)·B(x): NTT both onto a larger evaluation
   domain, multiply **pointwise**, inverse-NTT back.
3. *The quotient* H = P/Z: pointwise division on a coset — see B.3,
   where this becomes almost comically cheap.
4. (STARKs) the *low-degree extension*: re-evaluate the whole trace
   on a 2 to 8× larger domain — Reed–Solomon encoding, again NTTs —
   before Merkle-hashing and FRI.

**B.2 The transform itself, at size 4 in 𝔽₁₇.** The classical FFT
evaluates a polynomial at the complex n-th roots of unity
e^(2πik/n); the sines and cosines are merely how ℂ *parametrizes*
its roots of unity. The algorithm needs only three algebraic facts:
ωⁿ = 1, ω^(n/2) = −1, and "squaring the n-th roots gives the
(n/2)-th roots" (what lets the problem halve recursively). These are
radix-2 requirements, so n is always a power of two — circuits pad
to the next 2ᵏ with dummy constraints rather than ever running an
odd-length transform (mod 17 odd orders don't even exist:
every element order divides 16). Any
field with an element of order n runs the identical recursion —
exactly, with no rounding. In 𝔽₁₇, p − 1 = 16, so orders up to 16
exist; ω = 4 has order 4:

```
ω = 4:   ω¹ = 4   ω² = 16 ≡ −1   ω³ = 13   ω⁴ = 1
domain D = {1, 4, 16, 13}          (the 4th roots of unity mod 17)
```

Run it on Appendix A's own P(x) = 13x² + 12x + 9. Split by
even/odd coefficients — P(x) = E(x²) + x·O(x²) with E(y) = 9 + 13y
and O(y) = 12. Now watch the domain collapse: the four points
square pairwise onto just two values, 1² = 1, 4² = 16, 16² = 256 ≡
1, 13² = 169 ≡ 16 — so E and O need evaluating only at {1, 16} =
{1, −1}. That collapse *is* the halving. Combine with the
butterfly P(x) = E(x²) + x·O(x²) at each of the four x:

```
E(1) = 22 ≡ 5    E(16) = 9 + 208 ≡ 13     O ≡ 12 everywhere
P(1)  = E(1)  +  1·12 = 17  ≡  0     P(16) = E(1)  + 16·12 ≡ 10
P(4)  = E(16) +  4·12 = 61  ≡ 10     P(13) = E(16) + 13·12 ≡ 16
```

Six multiplications instead of the naive twelve (naively each
point costs three: x·x, 13·x², 12·x). At this size even the six
flatter to deceive — 13·1 and 1·12 are multiplications by 1, and
since 16 ≡ −1 and 13 ≡ −4, two more are negations or reuses — but
that is exactly the right lesson: the honest claim is asymptotic.
The recursion satisfies T(n) = 2·T(n/2) + O(n) = O(n log n)
against O(n²): invisible at n = 4, a ~10⁵× factor at n = 2²⁰.
(Note P(1) ≡ 0: x = 1 is one of Appendix A's constraint points, and
the transform *displays* constraint c₁ holding. Real systems put
**all** constraints on such a domain, so the whole R1CS check is
visible in one spectrum.) The inverse transform is the same
butterfly run with ω⁻¹ = 13 and a global factor n⁻¹ = 4⁻¹ ≡ 13.

**B.3 Why roots of unity: the vanishing polynomial collapses.**
Appendix A built Z(x) = (x−1)(x−2) by multiplying linear factors —
fine at 2 points, hopeless at 2²⁰. (We write D for the domain —
the letter H is already taken by the quotient polynomial; be
warned that much of the SNARK literature does the opposite, using
H for the domain and lowercase h(x) for the quotient.) On the
domain D above, the vanishing polynomial is simply

```
Z_D(x) = x⁴ − 1        (generally: xⁿ − 1 on an n-point domain)
```

one subtraction to evaluate anywhere. Better still, the quotient
H = P/Z is computed on a *shifted coset* g·D where Z never
vanishes — and there it is not merely cheap but **constant**: on
3·D = {3, 12, 14, 5} every point satisfies x⁴ = 3⁴ ≡ 13, so
Z_D ≡ 13 − 1 = 12 across the entire coset, and "divide by Z" is
one multiplication by 12⁻¹ ≡ 10. Appendix A's polynomial long
division becomes: NTT P onto the coset, scale by a constant,
inverse NTT.

**B.4 Two-adicity — why the proof fields look the way they do.**
A radix-2 NTT of size 2ᵏ needs an element of order 2ᵏ, i.e.
2ᵏ | p − 1. That single divisibility requirement shapes the field
zoo:

| field | p | p − 1 factors as | max radix-2 NTT |
|---|---|---|---|
| toy 𝔽₁₇ | 17 | 2⁴ | 16 |
| Goldilocks | 2⁶⁴−2³²+1 | 2³²·(2³²−1) | 2³² |
| BabyBear | 2³¹−2²⁷+1 | 2²⁷·3·5 | 2²⁷ |
| BN254-Fr | ~2²⁵⁴ | 2²⁸·(odd) | 2²⁸ |
| M31 | 2³¹−1 | 2·3²·7·11·31·151·331 | **2** |

M31 is the cautionary tale: two-adicity 1, no radix-2 domains at
all — the reason Circle STARKs [8] exist (they run the transform on
the unit circle x² + y² = 1 over 𝔽_p, which has 2³¹ points with
perfect 2-adic structure). Two further design notes. *Exactness*:
a floating-point FFT's rounding is harmless in signal processing
and fatal here — one wrong field element breaks the divisibility
identity — while the NTT is exact by construction. *Reduction
cost*: the NTT does one modular reduction per multiply, so proof
fields are engineered for cheap reduction (Goldilocks reduces with
shifts and adds; BabyBear/M31 fit 32-bit lanes and vectorize).

**B.5 Production scale.** Order-of-magnitude anchors (2026
practice). A single proof segment typically carries **2²⁰ to 2²⁴
constraints or trace rows** (≈10⁶ to 1.6×10⁷); STARK blowup factors
of 2 to 8× put the largest NTTs at 2²³ to 2²⁷ points — BabyBear's 2²⁷
ceiling is not an accident but the binding constraint (a 2²⁴-row
trace at blowup 8 uses the whole two-adic budget). A Groth16
prover runs ≈7 size-m FFTs plus 4 size-m multi-scalar
multiplications; STARK provers are NTT + hashing dominated.
Computations bigger than one segment shard into thousands of
segments whose proofs are aggregated by recursion. §3's zkML
numbers land here: one n = 4096 witness×witness product costs
1.23×10¹⁰ constraints under rank-48 recursion — ≈10⁴ segments of
2²⁰ — versus 6.87×10¹⁰ naive, a 5.6× cut in segments, NTTs, and
commitments alike; per-layer transformer matrices (2048 to 8192 on a
side) sit squarely in the §3 table's range. The division of labor
is exact: the NTT/commitment layer fixes the **cost per
constraint**, and the bilinear rank of §3 fixes **how many
constraints there are**. Lower rank does not speed up the
transform; it shrinks the transform.

**Measured on this machine (Apple M-series, 10 P-cores).** The
field-choice folklore, quantified: the same radix-2 transform, one
core, correctness gated (root orders, inverse round-trip, naive-DFT
cross-check at n = 8, polynomial product vs schoolbook):

| domain | Goldilocks, 1 thread | BN254-Fr, 1 thread | per-core ratio | BN254-Fr, 6 threads |
|---|---|---|---|---|
| 2¹⁴ | 1.1 ms | 2.8 ms | 2.5× | 2.9 ms |
| 2¹⁸ | 34 ms | 55 ms | 1.6× | 74 ms |
| 2²² | 0.68 s | 1.11 s | 1.6× | 0.23 s |
| 2²⁵ | 7.8 s | — | — | 2.4 s |

The 64-bit field's per-core advantage is 1.6–2.6× (largest while
the working set fits in cache); the 254-bit field claws wall clock
back only through arkworks' parallel FFT (4.7× at 2²², and *slower*
than its own single thread at mid-size domains where fork/join
overhead dominates) — parallelism a 64-bit implementation could
match. Measured under concurrent background load; the ratios, not
the absolutes, are the payload.

**What a new record would buy.** Prover time is ≈ NTT (m log m) +
commitments (m), so speedup tracks the constraint ratio (the log
factor barely moves). At n = 4096, folding in §3's exponents:

- a **rank-47 4×4** is a drop-in upgrade of today's best base:
  (48/47)⁶ ≈ **1.13× fewer matmul constraints** (13.5%) — at a 90%
  matmul share, ≈12% end-to-end prover time;
- a **rank-22 3×3** speeds 3×3-blocked pipelines by **1.40×** but
  still trails the rank-48 base (0.84×) — its value is scientific
  (first sub-23) and field-cartographic, not operational;
- a **rank-21 3×3** — the Strassen-beating line — would take over
  as the best known base outright: **1.99× over rank-23** pipelines
  and **1.19× over rank-48**, i.e. ≈19% fewer constraints, NTTs,
  and committed elements than anything available today.

End-to-end wall clock scales by the circuit's matmul share (80 to 95%
in typical zkML inference), Amdahl-style.

**Larger bases (records as of July 2026).** The 𝔽_p-valid records
above 4×4 — remember that mod-2 results do *not* transfer to odd
proof primes — are: 5×5: **93** and 6×6: **153** (Moosbauer–Poole
[20], explicitly "over arbitrary ground fields"); 7×7: **250**
(Sedoglavic [21], non-commutative, so any ring); 8×8: **336**
(= Strassen ⊗ rank-48; mod 2 has 329 = 7×47 — another instance of
the field divergence this paper's program probes). What beating
each by 1 or 2 buys same-base pipelines at n = 4096
(speedup = (r/(r−k))^(log_m 4096); wall clock × matmul share as
above):

| base | record r | exponent | −1 | −2 | overtakes rank-48 at |
|---|---|---|---|---|---|
| 5×5 | 93 | 2.816 | +5.7% | +11.9% | ≤ 89 |
| 6×6 | 153 | 2.808 | +3.1% | +6.3% | ≤ 148 |
| 7×7 | 250 | 2.837 | +1.7% | +3.5% | ≤ 229 |
| 8×8 | 336 | 2.797 | +1.2% | +2.4% | ≤ 332 |

Two readings. A −1 is worth more at smaller bases: the recursion
depth log_m n shrinks as m grows, so a 5×5 improvement compounds
through 5.2 levels at n = 4096 while an 8×8 one gets only 4. And
no −1 or −2 at these sizes overtakes the rank-48 4×4 base — the
nearest paths to a new best base run through 5×5 ≤ 89 (−4) and
8×8 ≤ 332 (−4; especially interesting because today's 336 is
*inherited* from rank-48 via Strassen, so any direct 8×8
construction at ≤ 332 would beat every 4×4-blocked pipeline at
once).

**The additions record — pricing the dual lever.** §4's caveat
made additions a second lever: they vanish from the constraint
count but re-enter twice. (i) *Witness generation* evaluates the
scheme's three linear networks; its cost scales directly with the
network op count, compounding over recursion exactly like the
classical additions recursion. (ii) *Circuit shape*: folding the
linear forms keeps constraints at r^d but densifies R1CS rows
multiplicatively per level, while materializing intermediates
keeps rows sparse at the price of ≈ (ops/32)·m extra *linear*
constraints — ≈10×m at today's op counts, which is why nobody
fully materializes; practice interpolates (materialize every few
levels), and every point on that tradeoff curve scales
monotonically with the op count. The record: [10]'s Appendix B
states **341 operations** for the rank-48 networks (L = 104,
R = 84 + 1 shift, P = 119 + 33 shifts; "PLinOpt generated" [25],
via greedy straight-line synthesis, kernel/factorization routes,
and Tellegen transposition, after an isotropy transformation
rationalized AlphaEvolve's complex scheme to dyadic
coefficients) — but the *living* record is better, twice over.
The SLPs distributed in the PLinOpt library's data directory [25]
(`github.com/jgdumas/plinopt`, snapshot 2026-07-07) improve on the
paper in two steps. First, `data/4x4x4_48_rational_*.slp`, for the
identical matrices, checker-verifies in this repository at **315**
(L = 104 + 4, R = 75 + 1, P = 110 + 21). Second — and easy to
overlook under its name — `data/4x4x4_48_accurate_*.slp`, a
*different* rank-48 decomposition distributed for its numerical
accuracy, checker-verifies at L = 80 + 4, R = 68 + 8,
P = 108 + 16 = **284 operations** (256 additions + 28 dyadic
constant-multiplications), and its matrix triple Brent-verifies
over ℚ as a true ⟨4,4,4⟩ scheme under the same index convention as
the rational triple (protocol calibrated on the known-good case).
The living record is therefore **284**, 57 operations below the
published 341 — the authors improved their own artifact past
their paper, and the numerically-accurate variant, not the
rational one, is the cheapest. The 284 transfers verbatim to every
odd-characteristic 𝔽_p: the divisions /2^k are multiplications by
the fixed field constants ((p+1)/2)^k, so over a proof field the
program is 256 additions plus 28 constant-multiplications — and
under the R1CS objective the constant-multiplications fold into
linear-combination coefficients for free (Appendix C), leaving
density and witness generation as the quantities the 256 adds
govern. Over Goldilocks the codegen'd 284-op networks
(`bench284r`, exactness gated at n = 16 and 64) measure 4–5%
faster witness generation than the 315-op networks at n = 64 and
n = 1024 — the expected dilution of a 10% linear-phase cut by the
multiplication core. Our own checker-gated searches have **not**
improved on the artifact — the best verified alternative
orientation reaches 365, sixty signed-permutation and forty
dyadic-sandwich orbit variants bottom out at 371 and 422
respectively, and an eight-hour CSE storm found nothing below the
rational triple's counts — and an
earlier in-repo "329" is on record as a counting artifact caught
by output-checker gating (a methodological cautionary tale the
repository preserves). **No nontrivial lower bound is known**, so
whether 284 is tight is open in both directions. What reductions
would buy if found: both sinks scale linearly, so a 250-op network
would be worth ≈12% and a 200-op network ≈30% *of the adds-driven
components* (rebased to 284) (witness generation and the density/materialization
tax) — constant-class wins, stacking freely with the
exponent-class wins above.

## Appendix C. Measured: the constraint predictions on a real Groth16 stack

We implemented the three gadgets — naive, Strassen 2×2:7, and the
rank-48 4×4 recursion with the Brent-verified DPS coefficients — as
R1CS circuits over BN254 (arkworks Groth16; `matmul/benchzk/`), and
measured. Two headlines: one vindication, one warning.

**Constraint counts land exactly on §3's formulas.** n = 4: 64 /
49 / **48** multiplication constraints — a 4×4 witness×witness
product proven in 48 constraints, as this paper's premise promises.
n = 16: 4096 / 2401 / 2304; n = 64: 262,144 / 117,649 / 110,592
(= n³, 7^log₂ⁿ, 48^log₄ⁿ). Proofs verify; additions and dyadic
scalings cost zero constraints, folding into linear combinations.

**Wall clock does not follow constraint count at small n — the
density tax is real.** Fully folded, the depth-3 rank-48 circuit's
rows carry the *compounded* linear-form support, and at n = 64 its
proving time loses to naive by 17.6× (42.9 s vs 2.5 s) despite
2.37× fewer constraints. The §4 materialization analysis, measured
as a schedule (materialize the top t levels' combinations as
witness rows, fold below):

| levels materialized | constraints | prove (s) |
|---|---|---|
| 0 (fold all) | 114,688 | 42.9 |
| 1 | 143,360 | 26.4 |
| **2 (optimum)** | **229,376** | **12.7** |
| 3 (materialize all) | 487,424 | 13.1 |

The hybrid optimum recovers 3.4× over naive folding — and still
loses to the naive gadget at this size, because Groth16's prover
tracks total matrix *nonzeros* more closely than row count, and
even single-level rank-48 rows are denser than naive's
three-entry rows. (The materialization row counts match the
per-level formula 112·Σ 48^(ℓ−1)·16^(d−ℓ) exactly.)

**At n = 256 (depth 4) the density tax becomes an inversion, then
a wall.** Naive: 16.8M constraints, setup 99 s, prove 119 s.
Strassen: 5.83M constraints — 2.9× fewer — setup 433 s, prove
389 s: **3–4× slower on 2.9× fewer constraints**, because at depth
8 its folded rows are dense enough that nonzeros, not rows, set
the price. The rank-48 gadget could not be measured at n = 256 at
*any* materialization level on this 64 GB machine: folded
configurations (matlv ≤ 3) balloon past a 190 GB footprint into
swap (resident memory reads ~14 GB while macOS compresses and
pages — a measurement hazard in its own right), and
materialize-everything (matlv 4) exceeded 46 GB resident during
synthesis. A ~128 GB-class machine is the entry ticket for
depth-4 rank-48 Groth16 at bounded density.

**The whole pipeline at one scale** (benchzk `--full`: witness
generation, NTTs at the actual proof-domain size, setup, prove,
verify; n = 64, six proving threads, background load — the
relative structure is the payload, and the idle-machine
materialization optimum above reproduces):

| gadget | constraints | domain | NTT fwd | setup | prove | verify |
|---|---|---|---|---|---|---|
| naive | 266,240 | 2¹⁹ | 27 ms | 1.4 s | 1.5 s | 0.23 s |
| Strassen | 121,745 | 2¹⁷ | 6.6 ms | 1.5 s | 1.4 s | 0.23 s |
| rank-48, matlv 0 | 114,688 | 2¹⁷ | 7.3 ms | 30.5 s | 27.7 s | 0.23 s |
| rank-48, matlv 1 | 143,360 | 2¹⁸ | 14 ms | 17.2 s | 17.0 s | 0.23 s |
| rank-48, matlv 2 | 229,376 | 2¹⁸ | 14 ms | 7.9 s | 8.6 s | 0.24 s |
| rank-48, matlv 3 | 487,424 | 2¹⁹ | 26 ms | 8.2 s | 8.9 s | 0.23 s |

Strassen at this depth is still density-benign (naive-class prove
on 2.2× fewer constraints — its inversion only appears at depth
8); rank-48's fewest-constraint config (matlv 0) is its slowest,
and the interior optimum at matlv 2 stands. Witness generation
(3.7–4.0 ms) and verification are scheme-independent here, and
the NTT column simply tracks domain size — Strassen's smaller
domain buys a 4× cheaper transform than naive's, a reminder that
constraint *count* still owns the transform even when density
owns the MSMs.

**Witness generation is friendlier territory.** The prover must
also *compute* the witness — every intermediate product, in the
clear, over the field — and here the same networks measure very
differently (bench315/bench315r; the 315-op PLinOpt SLPs codegen'd
to Goldilocks, exactness gated at every size — regenerating from
the 284-op accurate triple (Appendix B.5) improves these rank-48
times a further 4–5% at n = 64 and 1024 in back-to-back A/B):

| n | naive | blocked naive | rank-48 recursive | ratio vs blocked |
|---|---|---|---|---|
| 16 | 0.019 ms | 0.019 ms | 0.035 ms | 1.83 |
| 64 | 1.15 ms | 1.15 ms | 0.926 ms | **0.80** |
| 256 | 80.7 ms | 79.9 ms | 47.0 ms | 0.59 |
| 1024 | 6.30 s | 5.08 s | 2.32 s | **0.46** |
| 4096 | 936 s | 246 s | 83.0 s | **0.34** |

(Arithmetic tuned to the field's design: division-free Goldilocks
reduction via 2⁶⁴ ≡ 2³²−1, halving as shift-plus-fixup, doubling
as one modular add, `target-cpu=native` + LTO — ≈2.7× over the
first-cut build; a cache-blocked naive is the control, worth 20%
at n = 1024.) The crossover sits at n ≈ 64 (hybrid cutoff:
recurse to 16×16 tiles, naive below), and by n = 1024 the
recursion is 2.2× faster than the blocked control — the measured
ratio 0.46 sitting just above the pure multiplication-tree limit
(48/64)³ = 0.42, i.e. the 289-add linear phases are nearly fully
amortized. Adds are cheap CPU operations, so witness generation
inherits the exponent advantage at small n, long before the
commitment-side density crossover. At n = 4096 (measured once,
under background load) the ratio reaches **0.34** against the
blocked control — almost exactly the compounding prediction
0.46 × (48/64) = 0.345 — and 11.3× over plain naive; the
284-vs-315 A/B is within noise at this size.

**Machine-level witness generation: mult–add fusion, calibrated.**
The 𝔽_p analogue of fused multiply–add is *delayed reduction*:
accumulate 128-bit products as (lo, hi) pairs of 64-bit sums — two
plain adds per term — and reduce once per output. Microbenchmarks
on this machine (dependent-chain methodology, correctness gated on
10⁵ random dot products) price the scalar Goldilocks multiply at
9.3 ns, a deferred multiply-accumulate at 1.25 ns, the final
combine-and-reduce at 10.4 ns, and halvings/adds at 1.2–1.5 ns:
deferral is ~2.7× cheaper, and reductions ~1.7× dearer, than naive
op counting assumes. Under these measured constants a cost model
over the rank-48 linear networks (shift-aware, deferral-aware;
`machinecost.py`) *appeared to reorder the record book*: the
284-op accurate triple — whose every output path crosses a
halving, blocking deferral — modeled at 753 cycles per 4×4 tile,
while a 357-op triple from this repository's own optimizer, with a
fully deferrable product side, modeled at **705**. Three storm
searches over exponent-relabel moves confirmed the 284's blockers
are structural, and an 18-variant orientation×gauge sweep under
the calibrated score left the 705 incumbent standing. **Then the
measured implementation refuted the model.** We codegen'd the
deferrable network with true delayed reduction — products kept as
unreduced (lo, hi) pairs, u128 limb-sum accumulation, subtraction
by bound-tracked negation constants, one combine per output —
field-gated it against schoolbook on 20,000 random tiles, and
timed all paths (`bench705`): 284-scalar 282 ns/tile, ours-scalar
331 ns, ours-*delayed* **461 ns** — 1.63× *slower* where the model
said 0.94×. The diagnosis is instructive: dependent-chain
microbenchmarks price *latency*, but a 4×4 tile executes at
*throughput* — the out-of-order core overlaps 48 independent
multiply-reduce chains, hiding exactly the reduction latency that
deferral skips, while the delayed path forfeits that parallelism
to longer dependency chains and roughly doubled live register
state. At tile granularity, machine-optimal ≈ operation-minimal
after all: **the 284 is the measured-fastest rank-48
witness-generation path**, and delayed reduction stays where it is
already standard — long, all-positive dot products (it gates
correct and wins there), i.e. naive inner loops, not rank-48
product networks. A cost model earns trust only against silicon;
this one paid for its lesson in one afternoon.

**Reading.** The exponent advantage is real and the counts are
exactly as predicted; the *crossover* where it beats naive wall
clock on a Groth16-over-BN254 stack sits beyond n = 64 at bounded
density (constraint ratio 0.85 at n = 64 → 0.67 at 256 → 0.53 at
1024, against a ≈2 to 3× density constant), i.e. likely n ≳ 10³ —
LLM-scale matrices, per §3, not toy benchmarks. Three levers move
the crossover in: PLONKish custom gates that hard-code the 48
fixed combinations as selectors (density becomes free); STARK/AIR
stacks whose cost model is hashing-dominated rather than
nonzero-dominated; and lower-adds networks (B.5), which shrink the
density constant directly — the measured reason the adds record
matters. Reproducible from the repository (`benchzk`, fixed
seeds); n = 256 and a PLONKish port are the natural next data
points.

## Acknowledgments

This work was carried out in an extended interactive collaboration
with Claude (Anthropic; the Fable 5 and Opus 4.8 models), which
implemented the engines and drafted this text under the author's
direction and review.

## References

1. V. Strassen. *Gaussian elimination is not optimal.* Numer. Math.
   13:354 to 356, 1969.
2. E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev. *Scalable,
   transparent, and post-quantum secure computational integrity.*
   ePrint 2018/046.
3. A. Fawzi et al. *Discovering faster matrix multiplication
   algorithms with reinforcement learning.* Nature 610:47 to 53, 2022.
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
    multiplications.* arXiv:2506.13242. (The 341-operation SLP
    accounting is its Appendix B; scheme + SLPs distributed via
    PLinOpt's data directory [25].)
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
20. J. Moosbauer, M. Poole. *Flip graphs with symmetry and new
    matrix multiplication schemes.* ISSAC 2025; arXiv:2502.04514.
    (5×5:93 and 6×6:153, over arbitrary ground fields.)
21. A. Sedoglavic. *A non-commutative algorithm for multiplying
    7×7 matrices using 250 multiplications.* Preprint, 2017.
22. A. Rosowski. *Fast commutative matrix algorithms.* 2019,
    arXiv:1904.07683. (3×3 in 21 commutative products; odd-n tiles
    in n(n²+2n−1)/2.)
23. *Exploring commutative matrix multiplication schemes via flip
    graphs.* 2025, arXiv:2506.22113.
24. A. Novikov et al. *AlphaEvolve: a coding agent for scientific
    and algorithmic discovery.* 2025, arXiv:2506.13131. (Origin of
    the rank-48 scheme, over ℂ; no operation counts there.)
25. J.-G. Dumas, B. Grenet, C. Pernet, A. Sedoglavic. *PLinOpt, a
    library for optimizing linear programs.*
    github.com/jgdumas/plinopt.
