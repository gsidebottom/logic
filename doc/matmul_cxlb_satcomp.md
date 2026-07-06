# Shortest XOR Straight-Line Programs for 3×3 Matrix Multiplication: Benchmark Description

*Greg Sidebottom · Claude Fable 5*

*Benchmark description in the style of the SAT Competition proceedings.
Generator and all inputs: github.com/gsidebottom/logic
(`matmul/cxlb.py`, the C-side lower-bound generator — cxlb).*

## 1. Problem origin

A bilinear scheme multiplying two 3×3 matrices with 23 products
(Laderman 1976) evaluates 23 products of linear forms and combines
them into the 9 output entries. Its **additive complexity** — the
number of binary ± additions in a straight-line program, negation
free, no change of basis — has been driven down in a rapid recent
chain: 60 (Stapleton, Aug 2025), 59 (Mårtensson–Stankovski
Wagner–Stapleton), 58 (Perminov), and the current record **56**
(Sun, Apr 2026). Sun's 56 = 13 + 13 + 30 splits into two *input
sides* (provably optimal for his scheme, via chain-covering
structure) and an *output side* of 30 additions computing the 9
output forms from the 23 products.

Whether **55 additions** are possible is open. Our exhaustive
orbit-level analysis of all 17,376 de Groote classes of the public
Heule–Kauers–Seidl scheme database (exact input-side minimization
over every representative; see the repository's research notes)
reduced the question, for all known classes, to the output side:
**a 55-addition scheme in a known class requires an output side of
27 or fewer additions on specific representatives** — two below the
best output count ever observed at this format.

Any ℤ-coefficient output-side program reduces mod 2 to an XOR
straight-line program. Hence the decision problem

> **SLP(k):** *do k XOR additions suffice to compute the 9 given
> output forms (vectors in GF(2)^23) from the 23 inputs?*

yields sound lower bounds: **UNSAT at k proves the integer output
side needs ≥ k+1 additions**, and UNSAT at k = 27 on the right cells (§3) closes entire
equivalence classes for 55. These benchmarks
are therefore not synthetic: each boundary instance is a live
mathematical question, in the tradition of the matrix-multiplication
benchmarks contributed to past competitions by Heule et al. The
family also has a structural property of independent solver
interest: its parity constraints are *AND-guarded*, which defeats
current XOR/Gaussian reasoning (CryptoMiniSat's Gauss cannot engage
through the guards), while plain CDCL faces genuine parity
hardness.

## 2. Encoding

SLP synthesis in the style of Fuhs–Schneider-Kamp (SAT 2010),
simplified by unit-vector inputs. For steps t = 1..k:

- **Source selection.** Step t selects exactly two sources among
  the 23 inputs and steps 1..t−1: selector bits with an
  exactly-two constraint (sequential counter).
- **Values.** Value bits x[t][i] are parity-defined:
  x[t][i] = sel[t][base_i] ⊕ ⊕_{j<t} (sel[t][step_j] ∧ x[j][i]).
  Since inputs are unit vectors, the base contribution to bit i is
  the single literal sel[t][base_i]. The AND-guarded parities are
  materialized either as Tseitin chains (plain CNF) or as native
  XOR lines (CryptoMiniSat's `x` extension) — both emitted by the
  generator.
- **Outputs.** Each of the 9 forms must equal some step value
  (selector-guarded bit equalities; weight-1 forms may match an
  input).
- **Symmetry breaking** (optional, default on): all step values
  nonzero, and adjacent *independent* steps (t+1 does not consume
  t) must have strictly lexicographically increasing values. Sound:
  swapping adjacent independent steps preserves validity, so every
  program normalizes by bubble sort; padding above the minimum
  survives as a dependent chain. (Dead-step elimination is
  deliberately **not** used: with it, SAT is not monotone in k —
  odd-length padding can force a dead step — which corrupts
  minimum-finding by descent.)

At k = 29 with symmetry breaking the CNF has 25,799 variables and
91,426 clauses.

## 3. Instances and empirical hardness

An instance is determined by (γ tensor of a scheme representative,
k). The γ tensors come from the public database and the record
chain; the de Groote group action (sandwiching by GL(3,2)² on the
output tensor) makes the output form-set depend only on the pair
(R, P) of GL(3,2) matrices; each of the 168×168 = 28,224 pairs is a
**cell** — one concrete output-side instance of the class. So every
class supplies ~28k cells, and the instance supply is practically
unlimited, with k the hardness dial:

- **SAT phase** (k ≥ minimum): moderately easy — minutes at the
  minimum + 1; witnesses are extracted and replay-verified by the
  generator.
- **Deep UNSAT** (k well below minimum): easy.
- **Boundary** (k ∈ {min−1, min}): hard. On the two calibrated
  seed cells, no attempted configuration decides the boundary
  within 10–30 minutes (Apple M4 Pro, single core per solver):
  kissat (600 s and 1800 s), CaDiCaL (600 s), CryptoMiniSat 5
  (615 s, plain and native-XOR), Z3 4.16 on a word-level QF_BV
  formulation (600 s), and a kissat+cadical+CMS portfolio with
  symmetry breaking (900 s).

Calibrated seed cells (SAT witnesses verified; boundaries open):

| cell | forms weight | GF(2) minimum |
|---|---|---|
| `sun56` output side (record scheme) | 49 | ∈ {29, 30} |
| `cn120` output side (C = 28 rep of the record class) | 60 | ∈ {27, 28} |

Deciding either boundary advances the research question directly;
UNSAT at 27 on the fat-sides window cells of the record class
would, combined with the published exhaustions, make "no
55-addition scheme exists in the record class" a theorem with a
DRAT certificate.

## 4. Proposed benchmark set

Twenty instances spanning the phases: the two seed cells at
k ∈ {min−1, min, min+1}, the identity cells of the two other known
56-addition classes (`i12w219c23ci`, `i19w225c4efh`) at their
boundaries, and four fat-sides window cells of the record class at
k = 27, each with and without symmetry breaking. All are emitted
by:

```
python3 matmul/cxlb.py --bits <scheme.bits> --k <K> --dump out.cnf
python3 matmul/cxlb.py --bits <scheme.bits> --k <K> --dump out.xnf   # native XOR
```

(`--no-sb` disables symmetry breaking; scheme bits files are
committed in the repository.)

## 5. Availability

Generator, scheme inputs, verification tooling, and the research
notes are public at **github.com/gsidebottom/logic**. The submitted
instances may be used freely under the competition's standard
terms.

## References

- Y. Sun. arXiv:2604.27645 (2026). 56-addition rank-23 scheme.
- D. Perminov. arXiv:2512.21980 (2025).
- E. Mårtensson, P. Stankovski Wagner, J. Stapleton. arXiv:2601.05272.
- J. Stapleton. arXiv:2508.03857 (2025).
- M. Heule, M. Kauers, J. Seidl. *Local search for fast matrix
  multiplication.* SAT 2019; JSC 104 (2021).
- C. Fuhs, P. Schneider-Kamp. *Synthesizing shortest linear
  straight-line programs over GF(2).* SAT 2010.
- J. Boyar, R. Peralta. *A new combinational logic minimization
  technique with applications to cryptology.* SEA 2010.
- J. Laderman. Bull. AMS 82(1), 1976.
