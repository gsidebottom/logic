# gamma3 — accuracy screen of the 3×3 database against accurate_262

Question (2026-10-27): can the 17,376 rank-23 ⟨3×3×3⟩ classes of the
Kauers–Heule–Seidl database (`../dbcache/schemes.tgz`, fetched by
`../dbcheck.py fetch`) give a recursion level that is both fast and more
accurate than the ⟨4×4×4:48⟩ scheme accurate_262 (Dumas–Pernet–Sedoglavic;
`../fastmm`, paper `doc/matmul_4x4_rank48_accurate262.tex`)?  **No.**

Quantities, per scheme and role (P the factor set that computes the outputs,
L and R the other two; every cyclic rotation of a `.tab`'s three blocks is a
valid algorithm, so each class is scored in all three roles and the best is
kept): the growth factors γ∞,∞, γ∞,2, γ₂,₂ (DPS, arXiv:2506.19405 Def. 11),
γ₂ = Σᵢ ‖Lᵢ‖₂ ‖Rᵢ‖₂ ‖P∗,ᵢ‖₂ (the orbit objective of their construction),
DPS's Q₀ (the sum definition, paper eq. 3) and
amp = maxⱼ ½ √(Σᵢ pⱼᵢ² ‖Lᵢ‖₂² ‖Rᵢ‖₂²) (paper eq. 12, the quantity that
ordered the measured errors).  Exponents are log₃ of the factor, and
log₃(amp / (√3/2)) for amp, the classical 3×3 algorithm having amp = √3/2;
accurate_262's are the log₄ counterparts: γ∞,∞ 3.522, γ∞,2 2.250, γ₂,₂
3.250, γ₂ 3.636, amp 0.750 (2√2 against the classical 1).

## Result: no fast-and-more-accurate 3×3 level

### At the stored ±1 representatives (`screen3.py` → `db3_gamma.csv`)

| factor | database minimum | exponent | accurate_262 | exponent | classes under accurate_262's exponent |
|---|---|---|---|---|---|
| γ∞,∞ | 29 | 3.065 | 132 | 3.522 | 15,461 of 17,376 |
| γ₂,₂ | 29.2 | 3.072 | 90.5 | 3.250 | 8,246 |
| γ∞,2 | 13.11 (69 classes) | 2.342 | 22.63 | 2.250 | none (threshold 11.84) |
| amp | 2.693 | 1.033 | 2.828 | 0.750 | none (threshold 1.974) |
| γ₂ | 59.1 (Smirnov's class) | 3.713 | 154.6 | 3.636 | none (threshold 54.3) |
| Q₀ | 12 (17 classes); median 15, max 19 | | 34 | | all |

The ∞,∞ and 2,2 norms favor the sparse ±1 schemes, but the paper's
measurements track γ∞,2 and amp, and on those every representative loses:
the best exponent is 2.342 against 2.250 (amp 1.033 against 0.750).  Our
55-addition class (i19, `../external/i19-55adds-slp.txt`) is far worse at
its stored point: γ∞,2 20.74, amp 4.15, Q₀ 17.

### Over the classes' orbits (`orbit3.py` → `orbit3_minima.csv`, `.log`)

L-BFGS over (U, V, W) ∈ GL₃³ (27 parameters; smoothed maxima with
continuation in β; 8 starts; every role) for the 124 classes in the union of
the top 40 by each quantity (Smirnov's class among them), plus our i19:

| factor | orbit minima over the 124 | best class | exponent | under accurate_262's exponent |
|---|---|---|---|---|
| γ∞,2 | 10.06–11.69 | i107w191c34ef | 2.102 | 124 of 124 |
| amp | 1.78–2.06 | i30w183c23ci | 0.656 | 119 |
| γ₂ | 49.3–56.8 | i106w191c23ci | 3.548 | 115 |

Smirnov's class reaches 11.01 / 1.85 / 51.6 and i19's 11.13 / 1.84 / 50.6:
the floor is nearly the same for every class (within 15%), and the classes
known for few additions sit in the middle of it.  Every minimizer is a dense
irrational point, like the 21.41 point of the 4×4 paper, not an implementable
scheme: over the 1,125 minimizers (125 rows × 3 roles × 3 objectives) a
factor keeps 71–207 of its 207 entries nonzero (mean 192; 69% of the factors
are fully dense) and a point has 198–585 distinct absolute coefficients to
six decimals (mean 489), recorded in the CSV's `nnz`/`distinct` fields.
DPS's γ₂ objective has dense minima too (Laderman, Smirnov).  The local
minima vary a little between runs (floating-point nondeterminism in the
BLAS): a second run moved 37 of the 125 per-class minima by more than 10⁻³,
at most 0.28 in γ∞,2 and 0.002 in amp, and changed no count above.  The Hadamard route that produced
accurate_262 (an orthogonal isotropy with entries in Z[½]) is closed in
three dimensions: a² + b² + c² = 4ᵏ forces a, b, c even, so a 3×3 orthogonal
matrix over Z[½] is a signed permutation, where ½H₄ exists for 4×4.

### At equal product saving

A 4×4 level saves a quarter of the products, a 3×3 level 4/27, so equal
saving takes 1.794 3×3 levels per 4×4 level, and a 3×3 scheme's excess
growth over the classical algorithm, (γ/3)^1.794, must stay under
accurate_262's 22.63/4: γ∞,2 ≤ 7.88, γ∞,∞ ≤ 21.1, amp ≤ 1.55.  Even the
unattainable orbit minima miss these (10.07 and 1.78: 1.3–1.5× short).

### Speed (`cost3.py`)

The plan doc's fused-pass cost model at n = 8192 f32 (GEMM 0.328 s, one
D48 level's passes 0.027 s; GEMM streams and pipelines left out, so only
the comparison between shapes counts):

| plan | saving against the GEMM |
|---|---|
| one 4×4 level | 16.8% |
| two 4×4 levels | 10.8% |
| one 3×3 level | 7.5% |
| two 3×3 levels | 1.4% |
| three 3×3 levels | −35.6% |
| 4×4 then 3×3 | 5.9% |
| 3×3 then 4×4 | 7.8% |

A 3×3 level moves 32 blocks of size n/3 per 23 products where a 4×4 level
moves 64 blocks of size n/4 per 48: the pass cost per saved product is 1.5×
higher, and a second 3×3 level buys almost nothing.

## Where 3×3 could still pay

- Packing-fused implementations (plan item 4), where the transforms'
  nonzeros count: the ±1 schemes have 139–186 nonzeros over the three
  factors (mean 159) against accurate_262's 696.
- Sizes 3ᵏ·m, where a 3×3 level avoids padding.
- Q₀ 12–19 against 34, which the error bounds reward and the measurements do
  not.

## Open

A discrete search over dyadic isotropies, GL(3, Z[½])³, for exact points
below the ±1 representatives, bounded by the continuous minima (γ∞,2 ≥ 10.06
and amp ≥ 1.78 in these classes).  A point would need γ∞,2 ≤ 7.88 to matter
at equal speed, which the bound rules out: at best it would lower the error
of a 3×3 level for the 3ᵏ·m sizes.

## Files

- `screen3.py OUT.csv`: every database scheme and our two slp files
  (`../external/i19-55adds-slp.txt`, `i12-56adds-slp.txt`), all three roles
  → `db3_gamma.csv` (17,378 rows); about a minute.
- `orbit3.py db3_gamma.csv OUT.csv [--top 40] [--starts 8] [--jobs 12]`:
  the orbit minima → `orbit3_minima.csv` and the printed table
  `orbit3_minima.log` (124 classes); about 7 minutes on 12 cores.
- `cost3.py`: the shape cost table above.
- Convention (verified on the database): a `.tab` row holds the 3×3 blocks
  A | B | Cᵀ of one product, row-major; L = x, R = y, P = (z[:, T])ᵀ with
  T = [3j + i]; `orbit3.check` tests vec(AB) = P((L vec A) ⊙ (R vec B)) on
  random matrices before a role is scored.
