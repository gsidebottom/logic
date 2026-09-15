# Box-shaped structure in the SAT Competition 2025 and 2026 sets

*2026-09-14.  What the box backend could be pointed at, judged from the
instances themselves.*

## Method

The 400 instances of the 2025 main track (GBD tag `main_2025`) and the 400
of the 2026 selection (`tools/gbd/sc2026_selected_benchmarks.csv`) are all
in `~/projects/sat_benchmarks`.  `tools/cnf_structure.py` scanned the two
smallest instances of every family (250 instances, 149 families) for
structure a translator could detect from the CNF alone:

- **Tseitin gate definitions** — AND/OR gates of any width (a clause
  `o ∨ ¬a₁ ∨ … ∨ ¬aₖ` with the binaries `¬o ∨ aᵢ`), XOR2 (4 ternary clauses
  over 3 variables forbidding one parity class), XOR3 (8 clauses over 4),
  MAJ3 (6 clauses), and full adders (an XOR3 and a MAJ3 on the same
  inputs); `gate %` is the fraction of clauses in gate definitions.
- **Same-scope groups** — two or more clauses over one set of ≤ 12
  variables, the shape of a table constraint's direct encoding (one
  clause per forbidden tuple) and of a gate given as a relation;
  `scope %` is the fraction of clauses in such groups.
- The clause-length profile (`binary` = fraction of 2-clauses: the
  signature of pairwise at-most-one and other cardinality encodings).

Families were classed by medians: *circuit* (gate % ≥ 80), *table-like*
(scope % ≥ 80), *cardinality* (binary ≥ 0.80 and few gates),
*circuit+parity* (gates with XORs), else *mixed*.  Instance counts
(2025 + 2026): circuit 223, circuit+parity
67, table-like 88, cardinality
147, mixed 274.

## What maps to boxes, and where the backend can be expected to do well

**1. Circuits — the largest and cleanest target (290 instances,
~36 %).**  Hardware model checking, equivalence checking (plain, md5,
multiplier, miter, crafted-cec, circuit-equivalence), bitvector, RISC
instruction removal, CBMC, floating-point commutativity, polynomial
multiplication — and, unexpectedly, `belpyramid-puzzle`, the biggest
family of both years (32 + 30 instances), whose CNFs are 95–98 % 2-input
AND gates: an AIG of ~2 000–3 300 gates over ~130 inputs.  The mapping is
the one the design doc was written for: extract the gate definitions
(the scanner already does it by clause pattern), cut the gate DAG into
k-feasible cones (k ≤ 12–16 inputs), and compile each cone's function to
a table with the cone's internal gate outputs *hidden* — the ∃-projection
of §2.4, since a gate output is a function of the cone's inputs.  Arc
consistency on a cone's table is k-consistency on the circuit (strictly
stronger than unit propagation gate by gate — the adder measurements of
§1 are the special case of one full-adder cell), and the hidden gate
variables leave the search.  `sat --boxes` already takes a CNF plus box
instances (`{"table": <file>, "args": [dimacs vars]}`), so a
`tools/cnf2boxes.py` (gates → cuts → tables + residual CNF) plugs in
without engine changes.  Ranked by promise (structure × size the engine
can handle today):

- `multiplier-equivalence-checking` (12 + 12): 2.5 K vars, 8.5 K clauses,
  1 550 AND2 + 830 XOR2 — array/Booth multipliers in half-adder form.
  Famous for defeating CDCL (algebraic methods win); adder-cell and
  column-cone tables are the natural boxes and the smallest instances of
  the class.
- `miter` (6 + 6) and `circuit-equivalence-checking` (4 + 1): 2–3 K vars,
  AND + a few hundred XOR.
- `belpyramid-puzzle` (32 + 30): 2–4 K vars, pure AND — cut-boxing the
  whole puzzle; 62 instances make it the family where a win would count
  most.
- `bitvector` (2 + 3), `hardware-verification` (3 + 3): 6–50 K vars,
  mostly AND.
- `hardware-model-checking` (19 + 13): 50–70 K vars, AND with some XOR —
  BMC unrollings, exactly the shape the bmc composition experiment
  (§10.1) targets, but an order of magnitude above what the engine has
  been run on.
- `equivalence-checking` (12 + 16, 490 K vars) and `md5-equivalence-checking`
  (12 + 15, 7.6 M vars): the same shape at a scale the engine is not
  ready for.

**2. Same-scope (table-like) families (88 instances).**
`multiplier-verification` (4 + 12): every clause is in a ternary
same-scope group — gates given as 3-variable relations (a Tseitin
variant); each group is literally a table box, and cones compose.
`stedman-triples`, `hypertree-decomposition`, `tree-decomposition`,
`graceful-production`, `subgraph-isomorphism`: permutation / assignment
constraints over small scopes, where a table over the whole scope gives
arc consistency that unit propagation on the clauses lacks (the
all-different effect) — but graceful-production is 2.3 M variables and
ramsey-numbers' groups (clique clauses) gain nothing from tables.

**3. Parity families — a Gauss box, not a table.**  `tseitin-formulas`,
`xor-chain`, `purdom-instances`, `ordering-principle-xor`, `sat-x`,
`ssp-0`, `independent-set-reconfiguration` (238 K XOR gates),
`cryptography-simon`, `coloring-mycielski-graph`: XOR gates are the
easiest structure to detect (100 % of the clauses in tseitin-formulas),
but the SLP and Brent-equation results of §10.1 are decisive: arc
consistency on a parity table forces exactly what unit propagation on the
XOR clauses forces.  These families need Gaussian elimination
(CryptoMiniSat's edge over kissat/CaDiCaL) — a linear-system propagator as
a new box *kind*, which would be a genuine differentiator, but it is not
the table machinery.  Adders inside factoring / sum-of-3-cubes /
prime-factoring (XOR3 + carry) are the circuit case above.

**4. Cardinality / binary-clause families (147 instances) — no.**
Scheduling, school-timetabling, argumentation, p-center, oddball-weighing,
mechanical-master-key, station-repacking, set-covering, independent-set,
graph-isomorphism, puzzles with pairwise at-most-one: sequential-counter
and pairwise encodings on which unit propagation is already arc-consistent
(Sinz 2005).  A native cardinality propagator would only save auxiliary
variables; tables have nothing to offer.

**5. Mixed (274 instances)** — clique-coloring, coloring, planning,
sudoku (842 K vars), pigeonhole variants, waerden (ours): combinatorial
families where the encoding is mostly cardinality, and hard cores where
no propagation scheme matters.

## Bottom line

About a third of both competitions is circuits whose gate structure a
translator can read off the CNF, and that is the box backend's thesis in
its purest form (hidden internals, k-consistency over cones).  The next
step is `tools/cnf2boxes.py` and a measurement on the small circuit
families — multiplier-equivalence-checking, miter, belpyramid — before
anything else; the parity third would need a Gauss box, and the
cardinality third is not ours.  Caveat from §10.1: on the two families
measured so far the engine is 10–100× slower than CaDiCaL per search, so
the cones must change the *search*, not just the propagation, to matter.

## First measurement: `tools/cnf2boxes.py` on the three small circuit families

`tools/cnf2boxes.py` reads the gates off a CNF, merges single-fanout gates
bottom-up into cones of at most K inputs, hides the cones' internal gate
outputs, compiles each cone to a table (Quine–McCluskey cover of the
function and its complement; `--verify` re-evaluates every table), and
writes the residual CNF plus the instances for `sat -b boxes --boxes`.  On
the two smallest instances of each family it hides 40–70 % of the
variables and absorbs 50–90 % of the clauses in 0.1–0.6 s (K = 8; K = 12
takes up to 30 s in Python).  Four configurations per instance, 60 s cap
(2026-09-14, one core each): CaDiCaL on the plain CNF, the box engine on
the plain CNF (the engine alone, watched clauses), and the box engine with
K = 8 and K = 12 cones.

| instance | CaDiCaL | box engine, plain CNF | cones K = 8 | cones K = 12 |
|---|---|---|---|---|
| belpyramid c3540 (2,163 vars, ISCAS-85) | UNSAT 0.46 s | UNSAT 3.7 s (122 K conflicts) | UNSAT 6.6 s (212 K) | UNSAT 6.5 s (207 K) |
| belpyramid c5315 (3,801 vars) | UNSAT 0.16 s | UNSAT 1.7 s (57 K) | UNSAT 2.7 s (104 K) | UNSAT 2.9 s (101 K) |
| multiplier-equivalence bit28 / bit29 (2.5 K vars) | > 60 s | > 60 s | > 60 s | > 60 s |
| miter eq.atree.braun.13 (2.0 K vars) | > 60 s | > 60 s | > 60 s | > 60 s |
| miter lec_mult_CvW_11x10 (2.6 K vars) | > 60 s | > 60 s | > 60 s | > 60 s |

Two diagnostics on the ISCAS pair explain the slowdown.  Keeping *all*
original clauses next to the K = 8 cones (redundant tables) brings the
conflicts back to the plain count (c3540: 129 K, c5315: 62 K) at 30 %
more time — so the extra conflicts of the cones-only runs come from
*learning*: a table's lazy explanation (the assigned literals of the box
whose kill masks cover the dead rows, oldest levels first) is coarser than
the gate clauses it replaces, and the learned clauses are weaker.
And with the clauses present the tables prune nothing further: unit
propagation on AND/OR gates is already the cone's arc consistency for this
kind of circuit.  Emitting only cones of ≥ 4 gates changes neither.

What follows.  (1) Hidden internals are worth having only with
*minimal* explanations — a hitting-set minimisation of the kill-mask
explanation, or explaining a table's propagation through the cone's own
gate clauses kept as explanation-only clauses — that is the engine change
this experiment asks for.  (2) The propagation gain of cones needs
cones where arc consistency beats gate-level unit propagation — XOR- and
adder-rich cones, as in the multiplier and miter families — and those
instances are beyond 60 s for CaDiCaL too (the family wants algebraic
reasoning), so the comparison needs a larger budget or the adder-rich but
moderate `prime-factoring` / `sum-of-3-cubes` instances.  (3) On the
ISCAS-style AND circuits the box engine is 5–10× slower than CaDiCaL on
the plain CNF already; that gap is the engine's CDCL maturity, not the
boxes.

## Per-family scan (families with ≥ 2 instances across both years)

| family | 2025 | 2026 | class | vars (median) | AND gates | XOR gates | gate % | scope % | binary |
|---|---|---|---|---|---|---|---|---|---|
| belpyramid-puzzle | 32 | 30 | circuit | 2,982 | 2,663 | 0 | 96 | 0 | 0.67 |
| scheduling | 23 | 17 | cardinality | 239 | 2 | 0 | 1 | 24 | 0.83 |
| oddball-weighing | 20 | 18 | cardinality | 5,649 | 1,433 | 0 | 9 | 0 | 0.83 |
| argumentation | 20 | 15 | mixed | 1,000 | 498 | 0 | 33 | 7 | 0.96 |
| hardware-model-checking | 19 | 13 | circuit+parity | 59,604 | 36,698 | 3,858 | 76 | 30 | 0.47 |
| equivalence-checking | 12 | 16 | circuit | 488,786 | 381,787 | 67,479 | 100 | 18 | 0.58 |
| md5-equivalence-checking | 12 | 15 | circuit | 7,598,025 | 630,110 | 0 | 95 | 0 | 0.65 |
| mechanical-master-key | 12 | 14 | cardinality | 3,654 | 232 | 0 | 16 | 0 | 0.93 |
| p-center | 12 | 13 | mixed | 2,320 | 0 | 0 | 0 | 1 | 0.51 |
| school-timetabling | 12 | 13 | mixed | 215,266 | 2,632 | 0 | 3 | 4 | 0.38 |
| unknown-cases | 12 | 13 | mixed | 475 | 380 | 0 | 44 | 36 | 0.91 |
| multiplier-equivalence-checking | 12 | 12 | circuit | 2,557 | 1,548 | 833 | 93 | 46 | 0.36 |
| clique-coloring | 6 | 11 | mixed | 725 | 34 | 0 | 2 | 0 | 0.17 |
| multiplier-verification | 4 | 12 | table-like | 21,669 | 0 | 5 | 0 | 100 | 0.00 |
| miter | 6 | 6 | circuit | 2,287 | 1,944 | 319 | 100 | 18 | 0.55 |
| planning | 3 | 8 | mixed | 8,809 | 528 | 0 | 10 | 26 | 0.67 |
| tseitin-formulas | 6 | 4 | circuit | 273 | 0 | 164 | 100 | 100 | 0.01 |
| coloring | 4 | 5 | mixed | 286 | 21 | 0 | 3 | 0 | 0.21 |
| cryptography | 1 | 8 | table-like | 943 | 98 | 381 | 52 | 80 | 0.07 |
| hamiltonian | 4 | 4 | mixed | 300 | 240 | 0 | 44 | 36 | 0.91 |
| graceful-production | 7 | 1 | table-like | 2,344,880 | 13,461 | 0 | 2 | 92 | 0.07 |
| ramsey-numbers | 6 | 2 | table-like | 162 | 0 | 0 | 0 | 100 | 0.00 |
| set-covering | 5 | 2 | cardinality | 500 | 0 | 0 | 0 | 0 | 0.81 |
| algorithm-equivalence-checking | 7 | 0 | mixed | 3,169 | 1,173 | 34 | 32 | 57 | 0.37 |
| independent-set | 4 | 3 | cardinality | 14,879 | 445 | 0 | 3 | 20 | 0.80 |
| cryptography-simon | 5 | 2 | circuit | 2,768 | 528 | 1,584 | 86 | 81 | 0.24 |
| station-repacking | 2 | 5 | cardinality | 31,149 | 1,449 | 0 | 4 | 0 | 1.00 |
| hypertree-decomposition | 4 | 2 | table-like | 170,757 | 0 | 0 | 0 | 98 | 0.02 |
| grs-fp-comm | 5 | 1 | circuit | 89,200 | 40,294 | 33,205 | 98 | 53 | 0.31 |
| hardware-verification | 3 | 3 | circuit | 11,810 | 7,255 | 0 | 84 | 16 | 0.83 |
| stedman-triples | 3 | 3 | mixed | 2,093 | 96 | 0 | 1 | 73 | 0.02 |
| core-based-generator | 3 | 3 | mixed | 1,034,563 | 0 | 0 | 0 | 0 | 0.00 |
| sudoku | 5 | 0 | mixed | 842,147 | 0 | 0 | 0 | 1 | 0.66 |
| circuit-equivalence-checking | 4 | 1 | circuit+parity | 2,946 | 1,407 | 152 | 44 | 27 | 0.35 |
| polynomial-multiplication | 3 | 2 | circuit | 39,376 | 19,997 | 18,964 | 100 | 48 | 0.39 |
| bitvector | 2 | 3 | circuit | 32,624 | 24,883 | 2,892 | 100 | 8 | 0.61 |
| relativized-pigeon-hole | 3 | 2 | mixed | 850 | 0 | 0 | 0 | 0 | 0.34 |
| graph-isomorphism | 4 | 1 | cardinality | 42,048 | 0 | 0 | 0 | 0 | 1.00 |
| independent-set-reconfiguration | 4 | 1 | circuit+parity | 305,908 | 20,348 | 238,191 | 68 | 65 | 0.35 |
| risc-instruction-removal-subrv | 4 | 0 | circuit+parity | 5,438,623 | 297,451 | 1,079 | 45 | 56 | 0.29 |
| rooks | 3 | 1 | mixed | 113,356 | 44 | 0 | 0 | 0 | 0.25 |
| at-least-two-sol | 3 | 1 | mixed | 52,941 | 56 | 18,531 | 6 | 60 | 0.23 |
| waerden | 3 | 1 | mixed | 242 | 11 | 0 | 0 | 0 | 0.01 |
| baseball-lineup | 1 | 3 | mixed | 2,489,404 | 0 | 0 | 0 | 1 | 0.51 |
| sum-of-3-cubes | 1 | 3 | circuit+parity | 93,592 | 21,419 | 23,849 | 54 | 72 | 0.24 |
| battleship | 2 | 2 | cardinality | 265 | 0 | 0 | 0 | 0 | 0.88 |
| prime-factoring | 0 | 4 | table-like | 2,541 | 359 | 829 | 52 | 90 | 0.07 |
| sat-x | 3 | 0 | table-like | 1,004,426 | 3,028 | 86,760 | 34 | 96 | 0.01 |
| circuit-multiplier | 2 | 1 | mixed | 1,117 | 99 | 184 | 6 | 58 | 0.02 |
| ordering-principle-xor | 2 | 1 | table-like | 2,966 | 0 | 0 | 0 | 100 | 0.00 |
| hgen | 1 | 2 | mixed | 321 | 0 | 0 | 0 | 0 | 0.00 |
| hamiltonian-cycle | 2 | 1 | mixed | 30,757 | 4,023 | 0 | 5 | 64 | 0.12 |
| coloring-mycielski-graph | 1 | 2 | circuit+parity | 4,726 | 383 | 1,132 | 46 | 46 | 0.15 |
| subgraph-isomorphism | 1 | 2 | mixed | 370 | 10 | 0 | 0 | 50 | 0.50 |
| hidoku | 1 | 2 | mixed | 1,908 | 0 | 0 | 0 | 0 | 0.59 |
| edge-matching | 2 | 1 | mixed | 5,566 | 166 | 0 | 2 | 42 | 0.12 |
| rbsat | 2 | 1 | cardinality | 852 | 42 | 0 | 2 | 4 | 1.00 |
| puzzle | 1 | 2 | table-like | 3,355 | 55 | 0 | 1 | 100 | 1.00 |
| purdom-instances | 3 | 0 | table-like | 4,477 | 0 | 2,180 | 49 | 100 | 0.00 |
| ssp-0 | 0 | 3 | table-like | 29,921 | 58 | 10,081 | 46 | 96 | 0.21 |
| cryptography-cbmc | 0 | 3 | circuit | 272,659 | 181,090 | 56,096 | 94 | 18 | 0.72 |
| generic-csp | 1 | 2 | mixed | 1,156 | 0 | 0 | 0 | 0 | 0.00 |
| mutilated-chessboard | 1 | 2 | mixed | 652 | 336 | 0 | 59 | 0 | 0.84 |
| risc-instruction-removal-golcrest | 2 | 0 | circuit | 595,597 | 529,772 | 1,034 | 91 | 10 | 0.60 |
| crafted-cec | 2 | 0 | circuit | 25,039 | 25,011 | 0 | 100 | 0 | 0.67 |
| fpga-routing | 1 | 1 | cardinality | 230 | 0 | 0 | 0 | 0 | 0.98 |
| cellular-automata | 1 | 1 | mixed | 274,637 | 15,997 | 15,621 | 6 | 61 | 0.04 |
| software-verification | 1 | 1 | circuit | 1,904,324 | 124,433 | 152,834 | 83 | 46 | 0.49 |
| quasigroup-completion | 1 | 1 | mixed | 1,848 | 0 | 0 | 0 | 15 | 0.05 |
| circuit-equialence-checking | 2 | 0 | circuit+parity | 122,164 | 49,625 | 20,253 | 44 | 40 | 0.27 |
| diagnosis | 2 | 0 | mixed | 175,621 | 49,199 | 0 | 22 | 12 | 0.77 |
| coloring-clique | 1 | 1 | mixed | 662 | 33 | 0 | 2 | 0 | 0.20 |
| multiplier-circuits | 2 | 0 | table-like | 10,685 | 0 | 5,255 | 50 | 100 | 0.00 |
| grandtour-puzzle | 1 | 1 | circuit | 839 | 404 | 0 | 81 | 14 | 0.83 |
| reg-n | 2 | 0 | mixed | 4,608 | 0 | 0 | 0 | 0 | 0.21 |
| fixed-shape-random | 2 | 0 | mixed | 3,486 | 0 | 0 | 0 | 0 | 0.00 |
| knights-problem | 1 | 1 | mixed | 82,216 | 352 | 0 | 2 | 34 | 0.40 |
| summle | 1 | 1 | circuit+parity | 102,886 | 11,321 | 9,393 | 48 | 68 | 0.34 |
| random-csp | 2 | 0 | mixed | 647 | 40 | 0 | 2 | 46 | 0.51 |
| random-circuits | 2 | 0 | mixed | 1,864 | 0 | 0 | 0 | 50 | 0.00 |
| influence-maximization | 2 | 0 | mixed | 24,177 | 11,995 | 0 | 26 | 0 | 0.34 |
| erdos-discrepancy | 1 | 1 | mixed | 114,625 | 0 | 0 | 0 | 44 | 0.17 |
| cril-misc | 1 | 1 | circuit | 3,404,840 | 0 | 436,854 | 87 | 100 | 0.00 |
| termination-analysis | 1 | 1 | circuit | 17,299 | 16,499 | 427 | 82 | 38 | 0.64 |
| software-bmc | 0 | 2 | circuit+parity | 6,933,388 | 316,284 | 9,827 | 78 | 40 | 0.42 |
| agile | 0 | 2 | circuit | 29,442 | 14,790 | 13,921 | 99 | 54 | 0.33 |
| xor-chain | 0 | 2 | circuit | 202 | 0 | 134 | 100 | 100 | 0.00 |
| sliding-puzzle | 0 | 2 | circuit | 37,110 | 5,843 | 24,735 | 96 | 71 | 0.25 |
| or_randxor | 0 | 2 | mixed | 1,100 | 0 | 0 | 0 | 0 | 0.00 |
| floodit-puzzle | 0 | 2 | cardinality | 2,261,195 | 229 | 0 | 0 | 32 | 0.88 |
| register-allocation | 0 | 2 | cardinality | 292 | 0 | 0 | 0 | 0 | 0.99 |
| satcoin | 0 | 2 | table-like | 138,105 | 25,318 | 42,711 | 38 | 88 | 0.08 |
| minimum-disagreement-parity | 0 | 2 | circuit+parity | 918 | 59 | 441 | 70 | 66 | 0.10 |
| 01-integer-programming | 0 | 2 | table-like | 492,470 | 24 | 121,253 | 44 | 92 | 0.26 |
| auto-correlation | 0 | 2 | circuit+parity | 204,638 | 29,645 | 32,535 | 68 | 46 | 0.32 |
| tree-decomposition | 0 | 2 | table-like | 375,684 | 0 | 0 | 0 | 88 | 0.07 |
| ordering-principle | 0 | 2 | mixed | 1,325 | 0 | 0 | 0 | 0 | 0.01 |
| antibandwidth | 0 | 2 | mixed | 1,625,632 | 495,205 | 0 | 74 | 50 | 0.50 |
| alloy-vpn-models | 0 | 2 | mixed | 1,461,771 | 283,052 | 0 | 52 | 2 | 0.75 |
| cryptography-ascon | 0 | 2 | circuit | 142,894 | 16,789 | 70,838 | 100 | 84 | 0.11 |
| petrinet-concurrency | 0 | 2 | cardinality | 31,234 | 0 | 0 | 0 | 0 | 1.00 |
