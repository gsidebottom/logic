# Shortest XOR Straight-Line Programs for 3×3 Matrix Multiplication: Benchmark Description

*Greg Sidebottom*

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

**55 additions are now achieved** (13+14+28 on class i19w225c4efh),
by minimizing the output side *exactly* via the transposition
principle — the record was 56 (Sun 2026). That also gives, for every
scheme, the exact output-side minimum in milliseconds, so these
benchmark instances now come with **known ground-truth answers**
(the SAT/UNSAT boundary is independently pinned) while remaining hard
for every SAT/SMT solver we tried — an unusually clean combination for
a competition benchmark. The instances certify per-class optimality
and now target the next open question, **54**.

Any ℤ-coefficient output-side program reduces mod 2 to an XOR
straight-line program. Hence the decision problem

> **SLP(k):** *do k XOR additions suffice to compute the 9 given
> output forms (vectors in GF(2)^23) from the 23 inputs?*

yields sound lower bounds: **UNSAT at k proves the integer output
side needs ≥ k+1 additions** — an optimality certificate matching the
transposition-computed minimum. These benchmarks
are therefore not synthetic: each is a live
mathematical question with a known answer, in the tradition of the matrix-multiplication
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

Deciding a boundary certifies a per-class optimum: an UNSAT
certificate at the transposition-computed minimum proves a class's
output side cannot be smaller — a DRAT-checkable optimality theorem
for a fixed class, now that a 55 scheme is known and the target is 54.

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

## Appendix: a box-constraint realization, and tractable windows

The formulation of §2 is also realized, constraint for constraint, as a
formula over *box constraints* for the repository's matrix-method solver
(`lib/slp.jq`; the web app's *boxes* backend, `doc/box_backend_design.md`).
A box is a compiled table constraint called by name in the formula
language, `name(args)`, propagated to arc consistency — or, when the
table and its negation are tiny, as the equivalent clauses. Five boxes
suffice:

- `cnt2(u1;u2;s;v1;v2)` — one step of the sequential counter,
  v1 = u1 ∨ s, v2 = u2 ∨ (u1 ∧ s), ¬(u2 ∧ s); a chain from the constants
  (0,0) to (1,1) over the selectors s_t,0 … s_t,n+t−1 is "exactly two
  sources".
- `gx(p;s;x;q)` — q = p ⊕ (s ∧ x); a chain from s_t,i through the earlier
  steps is the AND-guarded parity
  x_t,i = s_t,i ⊕ ⊕_{u<t} (s_t,n+u ∧ x_u,i) (step 0's value bits are its
  input selectors).
- `imp(a;b)` — a ⇒ b; `imp(o_f_t; x_t_i)` or `imp(o_f_t; x_t_i')` per bit
  is the selector-guarded equality of form f with step t's value.
- `orb(p;o1;…;o7;q)` — q = p ∨ o1 ∨ … ∨ o7; a chain ending in the
  constant 1 is "at least one" (some step matches the form; every step
  value nonzero).
- `lexstep(e;g;a;b;e2;g2)` — e2 = e ∧ (a = b), g2 = g ∨ (e ∧ ¬a ∧ b); a
  chain over the bits from n−1 down, from (1,0), then
  `imp(s_{t+1}_{n+t}'; g)`, is the lexicographic symmetry breaking of
  adjacent independent steps.

Forms of weight 1 are dropped (an input computes them). An instance is
`{n, forms}`; `slp(inst; k)` generates SLP(k) with symmetry breaking,
`slp(inst; k; false)` without. The seed cells' output forms are embedded
as data (`sun56_cell`, `cn120_cell`, `i19_cell`, `i12_cell`, read from
the `.bits` files as `cxlb.py` reads them) together with Strassen's output
side over GF(2) (`strassen_out`: 4 forms over 7 products);
`slp_window(cell; [indices])` restricts a cell to the chosen forms over
the inputs they use. The same formula serves CaDiCaL: the web app expands
the calls into their definitions and Tseitin-encodes them, so both engines
see the identical constraint set (for the main instances the generator's
own CNF remains the reference).

**Reading a program off a witness.** `tools/slp_program.py` runs an
instance on either engine, reads each step's two sources from the s_t,j
of the witness, replays the program over GF(2)^n and checks that every
form is the value of some step (the replay verification of §3). Three
runs — Strassen's output side needs exactly 8 additions over GF(2):

```
$ tools/slp_program.py strassen_out 8
boxes backend: SLP(8) on strassen_out (n = 7, 4 forms of weight >= 2, 576 boxes): SAT in 0.18s
y1 = x1 + x2    = 1100000
y2 = x3 + y1    = 1110000
y3 = x2 + x4    = 0101000
y4 = x3 + x5    = 0010100
y5 = x6 + y2    = 1110010
y6 = x7 + y1    = 1100001
y7 = x5 + y6    = 1100101
y8 = y3 + y7    = 1001101
form 1001101: y8
form 0010100: y4
form 0101000: y3
form 1110010: y5
replay: every form computed

$ tools/slp_program.py strassen_out 7
boxes backend: SLP(7) on strassen_out (n = 7, 4 forms of weight >= 2, 472 boxes): UNSAT in 0.47s

$ tools/slp_program.py 'slp_window(sun56_cell; [0, 5, 7])' 8 --cadical
CaDiCaL: SLP(8) on slp_window(sun56_cell; [0, 5, 7]) (n = 11, 3 forms of weight >= 2, 794 boxes): SAT in 0.26s
y1 = x5 + x6    = 00001100000
y2 = x9 + y1    = 00001100100
y3 = x7 + x10    = 00000010010
y4 = x3 + y3    = 00100010010
y5 = x1 + x11    = 10000000001
y6 = x8 + y5    = 10000001001
y7 = x2 + y6    = 11000001001
y8 = x4 + y7    = 11010001001
form 00001100100: y2
form 11010001001: y8
form 00100010010: y4
replay: every form computed
```

**Tractable windows.** `tools/slp_bench.py` descends k with CaDiCaL to
each instance's minimum and times both engines at min−1, min, min+1
under a 60-second cap (run of 2026-09-15, with the engine's minimal
hitting-set explanations, decision heap and learned-clause minimisation;
Apple M4 Pro, one core per solver, times as the web app reports them).
Each cell is k = min−1 / min / min+1.

| instance | n | weights | k | boxes backend | CaDiCaL |
|---|---|---|---|---|---|
| strassen_out | 7 | 4,2,2,4 | 7 / 8 / 9 | UNSAT 0.4 s / SAT 0.1 s / SAT 0.01 s | UNSAT 0.2 s / SAT 0.01 s / SAT 0.04 s |
| sun56[0,3,7] | 9 | 3,3,3 | 5 / 6 / 7 | UNSAT 0.01 s / SAT 0.00 s / SAT 0.03 s | UNSAT 0.02 s / SAT 0.01 s / SAT 0.02 s |
| sun56[0,5,7] | 11 | 3,5,3 | 7 / 8 / 9 | UNSAT 1.2 s / SAT 0.07 s / SAT 0.03 s | UNSAT 0.3 s / SAT 0.2 s / SAT 0.1 s |
| i12[0,1,3] | 11 | 3,5,3 | 7 / 8 / 9 | UNSAT 1.3 s / SAT 0.02 s / SAT 1.3 s | UNSAT 0.3 s / SAT 0.4 s / SAT 0.2 s |
| i19[4,6,7] | 11 | 3,5,3 | 7 / 8 / 9 | UNSAT 1.0 s / SAT 0.01 s / SAT 0.01 s | UNSAT 0.3 s / SAT 0.3 s / SAT 0.2 s |
| cn120[0,6,8] | 9 | 5,5,3 | 7 / 8 / 9 | UNSAT 1.2 s / SAT 0.5 s / SAT 0.2 s | UNSAT 0.2 s / SAT 0.5 s / SAT 0.2 s |
| i12[0,3,4] | 12 | 3,3,7 | 9 / 10 / 11 | > 60 s / SAT 4.9 s / SAT 0.8 s | UNSAT 10.1 s / SAT 0.4 s / SAT 0.4 s |
| sun56[1,2,4] | 14 | 7,7,7 | 13 / 14 / 15 | > 60 s / > 60 s / SAT 23.0 s | > 60 s / SAT 15.7 s / SAT 58.3 s |

Windows of three forms with n ≤ 12 and minimum ≤ 10 are decidable by
both engines within the budget, which places them well below the seed
cells of §3 on the hardness dial. The box engine refutes the min−1 rows
in 0.4–1.3 s where CaDiCaL needs 0.2–0.35 s; on the satisfiable rows it
is 3–28× faster than CaDiCaL on six (i19[4,6,7] at k = 8 in 0.01 s
against 0.28 s) and 7–14× slower on three (i12[0,3,4] at k = 10 in
4.9 s against 0.43 s), and it solves the window of three weight-7 forms
at k = 15 in 23 s where CaDiCaL takes 58 s; the n = 12 boundary (CaDiCaL
10 s) and that window's k = 13 and 14 rows are beyond it. The
AND-guarded parities defeat table *propagation* exactly as they defeat
Gaussian elimination — arc consistency on the `gx` chains forces nothing
that unit propagation on the same clauses does not — and with the
engine's earlier trail-order explanations the satisfiable rows were
30–150× slower than CaDiCaL. What the tables contribute is the
*explanation*: a minimal hitting-set reason of two or three literals
where the trail-order one was longer, and correspondingly stronger
learned clauses.

## Acknowledgments

This work was carried out in an extended interactive collaboration
with Claude (Anthropic; the Fable 5 and Opus 4.8 models), which
implemented the repository's search tooling, exact minimizers, the
Lean formalization, and much of this text under the author's
direction and review. Every computational claim is mechanically
checkable by the commands in the reproduction section; the results
rest on those independent verifications rather than on trust in
either the author or the tools.

## References

- Y. Sun. *An Exact 56-Addition, Rank-23 Scheme for General 3×3
  Matrix Multiplication.* arXiv:2604.27645 (2026).
- A. I. Perminov. *A 58-Addition, Rank-23 Scheme for General 3×3
  Matrix Multiplication.* arXiv:2512.21980 (2025).
- E. Mårtensson, P. Stankovski Wagner, J. Stapleton. *A Rank 23
  Algorithm for Multiplying 3×3 Matrices with an Arithmetic
  Complexity of 59.* arXiv:2601.05272 (2025).
- J. Stapleton. *A 60-Addition, Rank-23 Scheme for Exact 3×3 Matrix
  Multiplication.* arXiv:2508.03857 (2025).
- M. Heule, M. Kauers, J. Seidl. *Local search for fast matrix
  multiplication.* SAT 2019; JSC 104 (2021).
- C. Fuhs, P. Schneider-Kamp. *Synthesizing shortest linear
  straight-line programs over GF(2).* SAT 2010.
- J. Boyar, R. Peralta. *A new combinational logic minimization
  technique with applications to cryptology.* SEA 2010.
- J. Laderman. Bull. AMS 82(1), 1976.
