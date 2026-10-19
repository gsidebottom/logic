# x47 — XOR count of rank-47 ⟨4×4×4⟩ schemes over F₂

Goal: a rank-47 mod-2 scheme for 4×4 matrix multiplication whose three
linear maps cost fewer than **170 XORs** in total, the best known count
(PLinOpt `data/4x4x4_47_mod_2_{L,R,P}`, cited by Dumas, Pernet,
Sedoglavic, Stapleton, Tichavský, arXiv:2609.12027).

A scheme is L (47×16, A side), R (47×16, B side) and P (16×47, output
side) with Vect(C) = P·((L·Vect(A)) ⊙ (R·Vect(B))), row-major vectors.
Cost = XOR(L) + XOR(R) + XOR(P), and by the transposition principle
XOR(P) = XOR(Pᵀ) + 31.

## Current best: 167 = 44 + 49 + 74 (`best/x167/`)

A point in the Kauers–Moosbauer class's symmetry orbit found by
simulated annealing (`xor47 orbit --anneal`), with the R side from the
exact helper search (Boyar–Peralta gives 50 there; the exact minimum
is 49); L and Pᵀ are exactly optimal as well (`xor47 exact`).
Checked by `x47check.py` (each program computes its matrix; the scheme
passes all 256 basis-pair Brent checks) and by PLinOpt's
`SLPchecker -q 2`.

Earlier: 168 = 44 + 44 + 80 (`best/x168/`), the reference scheme itself
(`ref/`, PLinOpt's 170) with Boyar–Peralta programs.

## Exact side minimization

A program for a target set T costs |T| + h, h = number of non-target
("helper") signals.  Every target that is the XOR of two available
signals can be added at no loss, so a solution is a helper sequence
whose closure covers T; iterative deepening on h (`xor47 exact`) is
exact and fast while h ≤ 4.  At the AlphaTensor-class 168 point it
proves Boyar–Peralta optimal on every side (44, 48, 45).

## Tools

- `../../src/bin/xor47.rs`: `xor47 bp|scheme|orbit`. Boyar–Peralta
  with exact distances from a 2¹⁶ table, `--slack/--p` randomized tie
  breaking, `--pilot W` lookahead, unused-gate removal, PLinOpt-syntax
  output, Tellegen transposition for P. `orbit` searches the scheme's
  symmetry orbit (A→XAY⁻¹, B→YBZ⁻¹ over GL(4,2), plus the six
  cyclic/transpose slot symmetries) by coordinate descent with random
  restarts, every point Brent-gated.
- `x47check.py`: independent checker (counts, matrices, Brent).
- `scheme47.py`: .bits ↔ sms conversion, Brent check, class invariant
  (rank-triple multiset up to slot permutation).

## Whole-orbit lower bounds (`xor47 lbscan`)

The scans and refinements above are exhaustive under Boyar–Peralta but
exact only near each scan minimum.  `lbscan` proves lower bounds on
every coset pair (distinct non-unit targets, plus one when the inputs'
closure misses a target, then the exact helper search one level at a
time, only for target sets in a coset triple that could still fall
below the target) and checks all 840³ triples, which covers the whole
orbit.  `lbclimb.sh` raises the target one step at a time on a shared
checkpoint: each step needs deep search on only tens of sets, where
aiming at 167 directly would raise about 10⁵ sets per level.

**Kauers–Moosbauer class (`seeds/km47`): every orbit point costs at
least 162** (2026-10-19; the class contains the 167).  Cheap bounds
give 144; levels 1–2 on 1.5·10⁶ sets give 150; the climb then proved
151–162, the later steps needing level-5 and level-6 refutations of
up to an hour each with the parallel search (`lbkm/climb.txt`; 161
took 1.9 h, 162 took 3.2 h, and 163 needs level-5 tests on ~150 sets).  The
older search (`xor47 lbcheck1`, `exact_dfs`) re-proved a seeded sample
of the refutations: 200/200 at level 4, 8/8 at level 5, and 51/51
exact sets (`lbkm/lbcheck1_*.log`).

## Classes tried (best orbit point found)

| class | given | best | sides L + R + P |
|---|---|---|---|
| PLinOpt reference (`seeds/ref47`) | 168 | 168 | 44 + 44 + 80 |
| AlphaTensor 47 (`seeds/at47`) | 179 | 168 | 44 + 48 + 76 |
| Kauers–Moosbauer 47 (`seeds/km47`) | 186 | **167** | 44 + 49 + 74 |

(Annealing: all 24 chains per class end at 168 under Boyar–Peralta
scoring; the 167 needs the exact search on one side.)

All three are flip-isolated (no two products share a factor), so plain
flip walks cannot leave them; a rank-47 walk with up-and-down excursions
(`flip 4 4 4 --walk --rank 47`, max excess 2) found nothing new in 5 min.
