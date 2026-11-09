# x47 — XOR count of rank-47 ⟨4×4×4⟩ schemes over F₂

Goal: a rank-47 mod-2 scheme for 4×4 matrix multiplication whose three
linear maps cost fewer than **170 XORs** in total, the best known count
(PLinOpt `data/4x4x4_47_mod_2_{L,R,P}`, cited by Dumas, Pernet,
Sedoglavic, Stapleton, Tichavský, arXiv:2609.12027).

A scheme is L (47×16, A side), R (47×16, B side) and P (16×47, output
side) with Vect(C) = P·((L·Vect(A)) ⊙ (R·Vect(B))), row-major vectors.
Cost = XOR(L) + XOR(R) + XOR(P), and by the transposition principle
XOR(P) = XOR(Pᵀ) + 31.

## Current best: 166 = 44 + 48 + 74 (`best/x166/`, 2026-11-08)

Two points in the symmetry orbit of the fifth rank-47 class
(`seeds/projkm47_7`, reached the night before by the flip descent from
Kauers–Moosbauer's <4,4,5>:60 projection pool, matmul/tomar_line): coset
triples (34f1, 1e25, 163d) with L 44 + R 48 + P 74 (`x166a_*`) and (135c,
7831, 79a8) with L 43 + R 48 + P 75 (`x166b_*`).  The fresh +4 orbit scan
put the class's heuristic minimum at 167 (3 of the 840 X-cosets; 4493
triples within +4); the refine confirmed 167 at 32 triples and 168 at 251;
a settle of those 283 triples (174 distinct open sides, depth 12, cap
600 s, 26 min) took the R side of both points from Boyar–Peralta's 49 to
the exact 48, and at both points all three sides are exact, so 166 is exact
there.  The full window followed at target 166 (4493 triples: depth 8, cap
600 s, 1491 sides, 2 h 22 min, 108 points left open below 166; depth 12,
cap 60 s, 2 min, none left), so **166 is exact over every coset triple
within +4 of the scan minimum, and exactly these two triples reach it**.
Checked by
`x47check.py` (each program computes its matrix; both schemes pass all 256
basis-pair Brent checks) and by PLinOpt's `SLPchecker -q 2`, three rounds
per program; both schemes are exactly equivalent to the class representative
(tomar_line/proj/scheme_iso.py).  Details in `best/x166/README.md`.

Earlier: 167 = 44 + 49 + 74 (`best/x167/`, 2026-10-17).
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

**Published class (`seeds/ref47`, the AlphaEvolve scheme): every orbit
point costs at least 160** (2026-10-19, `lbclass.sh ref47 143`: pre-raise
142 → 148, climb 149–160 in 3 h; the 161 step left one coset triple open,
the published scheme itself, whose output side (34 targets, heuristic 49)
the exact search could not decide at level 7 within an hour;
`lbref47/climb.txt`).  As a by-product the climb settles the published
scheme's input sides: six helpers are refuted on L and on R and
seven-helper programs exist, so XOR(L) = XOR(R) = 44 exactly (L does not
admit 43); its output side is proved ≥ 41 (heuristic 49), so the scheme
itself costs between 160 and 168.

**Projection-descent class (`seeds/proj47_5`): every orbit point costs
at least 163** (2026-11-07, `lbclass.sh proj47_5 152 167`; the cheap stage
alone gave 151 the day before, depth 2 on 363,591 sets, 13 min on 3
efficiency-core threads, `out/lbproj47_5/preraise_cheap_3threads.log`; the
climb proved 152-162 in 6.5 h with the 161 and 162 steps an hour each;
the 163 step took 7.3 h over two runs: the first, with a 12,600 s budget,
did levels 3-4 in five minutes and eleven level-5 refutations of 17-27
min each and stopped at 13,389 s with 6 coset triples open on one side
(`out/lbproj47_5/t167/climb_t163_budget12600.log`); the second, resumed
from the shared checkpoint with a 21,600 s budget and a 5400 s cap per
level test, proved it in 12,787 s with five more level-5 refutations, one
level-6 timeout at the cap and a level-7 refutation that closed the last
triples (`climb_t163.log`).  A 164 step is estimated at 30-60 h and is
not attempted).  With its best known point at 171 the class's window is
163-171, against 160-168 for the published class, 162-168 for
AlphaTensor's and 163-167 for Kauers-Moosbauer's.
How the 171 was found and settled: the BP orbit scan (`out/scan_proj47_5`, all 840^3 coset
triples, 63 min) puts the orbit minimum under BP at 171 with 411 triples
within +2 as collected (the scan's per-X candidate list was cleared on
every new per-X best, dropping triples still within the window: 646 lie
within +2, 7698 within +4, found 2026-11-07 from the saved tables and
fixed; the minimum and the 52 triples at 171 are unaffected), the exact
refine of those 411 triples (`out/scanref_proj47_5.log`)
gives 171 = 44 + 45 + 82, and `settle --depth 5 --cap 300`
(`out/settle5_proj47_5.log`, 57 min) proves eight triples exactly 171 and
leaves 78 of the 411 open below it; `settle --depth 6 --cap 1200`
(`out/settle6_proj47_5.log`, 20 min) settles 28 more sides exactly and
leaves 57 points open below 171; `--depth 8 --cap 2400`
(`out/settle8_proj47_5.log`, 48 min) settles 40 more exactly (eight one
below BP) and leaves one point open below 171 (total 173, bound 170),
through the one side that times out at every cap (43 targets, BP 50,
bound 47); settle's new bottom-up pass (after the top level's timeout it
climbs from level 0; `out/settle8b_proj47_5.log`) refutes that side's
levels 0-5 in two seconds, so it costs 49 or 50 and the point is at least
172: all 411 collected candidates settled, eight triples at 171
(2026-11-07); the 235 missed +2 triples and the +3/+4 ones (7698 in all)
are being refined and settled from the saved tables (Queue 6b, from
2026-11-07 18:00, then Queue 7's depth-12 settle, `deep_settle.zsh`).

**Kauers–Moosbauer class (`seeds/km47`): every orbit point costs at
least 163** (2026-10-19; the class contains the 167).  Cheap bounds
give 144; levels 1–2 on 1.5·10⁶ sets give 150; the climb then proved
151–163, the later steps needing level-5 to level-7 refutations of
up to an hour each with the parallel search (`lbkm/climb.txt`; 161
took 1.9 h, 162 3.2 h and 163 6.6 h, so each step costs about twice
the last).  The
older search (`xor47 lbcheck1`, `exact_dfs`) re-proved a seeded sample
of the refutations: 200/200 at level 4, 8/8 at level 5, and 51/51
exact sets (`lbkm/lbcheck1_*.log`).

**Kauers–Moosbauer class, the +4 window of its orbit scan settled: no
point below 167** (2026-11-07, Queue 6b).  The scan's saved side tables
re-emit the 1824 coset triples within +4 of the BP minimum (the October
scan collected 100 of the 131 within +2; `out/scan4_km47`); `refine`
with BP 1000 runs and the bottom-up exact pass at cap 30 s (55 min,
`out/scanref4_km47.log`) finds nothing below the record's count, 167,
which two triples reach (one as 43 + 49 + 75); `settle --depth 8 --cap
600` (71 min, `out/settle4_km47.log`) proves all but 25 points at least
167, the 25 open only through 16 sides whose BP programs sit 9 or 10
helpers above their target counts, beyond the depth (641 open sides, 625
within it); `settle --depth 10 --cap 60` on the same side cache (92 s,
`out/settle4b_km47.log`, the recipe is `deep_settle.zsh`) settles them:
15 exactly within seconds, four of them one or two below BP inside
points of 169 or more, and one at BP 53 with floor 52 after the
bottom-up pass refuted levels 0-8, leaving no point open below 167.  So
167 is exact over every coset triple within +4 of the scan minimum; a
166 in this class would need exact gains of at least 6 over the BP
counts across the three sides of a triple whose BP total is 172 or more
(the largest single-side gain seen in the window is 2).  The whole-orbit
bound stays 163.

**The other classes' +4 windows (Queues 6b and 7, 2026-11-07 18:00 to
2026-11-08 13:31).**  Same pipeline as km47's: scan +4 from the saved side
tables, refine (BP 1000 runs + bottom-up exact per side, cap 30 s), settle
depth 8 cap 600 s, deep settle depth 12 cap 60 then 600 on what stays open.
AlphaTensor's class: 3844 triples, best 168, exact over the window (the depth-8
settle was starved by a runaway scan and died at its 5 h timeout with 434 of
1044 sides done; the depth-12 pass finished the rest from the cache in 4 min,
none open).  Projection-descent class: 7698 triples, best 171, exact over the
window (depth 8: 4.9 h, 79 points open; depth 12: none).  AlphaEvolve's class
(`seeds/ref47`): 2882 triples, best 168, 30 points still open below 168 after
depth 12 at cap 600, every one of them only through the published scheme's own
output side (34 targets, BP 49, proved floor 39, 14 helpers to decide; the
`lbref47` climb could not decide its level 7 within an hour) or a 37-target
cousin (BP 52, floor 42, 14 helpers); their floors leave totals of 158-162
nominally possible, which is a statement about the depth of that side, not
evidence of a program.  Windows, whole-orbit bound to best program: fifth
class none-166, Kauers–Moosbauer 163-167, AlphaTensor 162-168, AlphaEvolve
160-168, projection-descent 163-171.

## Classes tried (best orbit point found)

| class | given | best | sides L + R + P |
|---|---|---|---|
| PLinOpt reference (`seeds/ref47`) | 168 | 168; 30 of its 2882 window triples stay open below 168, all through the published scheme's output side (34 targets, BP 49, floor 39) and a 37-target cousin (2026-11-08) | 44 + 44 + 80 |
| AlphaTensor 47 (`seeds/at47`) | 179 | 168, exact over its +4 window (3844 triples, 2026-11-08) | 44 + 48 + 76 |
| Kauers–Moosbauer 47 (`seeds/km47`) | 186 | 167 | 44 + 49 + 74 |
| projection-descent 47 (`seeds/proj47_5`, 2026-11-06: matmul/tomar_line/proj/found47/r47-00005, a fourth class by the rank-triple invariant and the exact test tomar_line/proj/scheme_iso.py, which puts 6 of our 27 descent 47s in it) | 180 | 171, exact at 8 triples (anneal 22/24 chains; exhaustive BP scan 171, 411 triples within +2; exact refine 171; settle depth 5 leaves 78 triples open below 171, depth 6 57, depth 8 one, the bottom-up pass none: 171 exact over all 411; the full +4 window, 7698 triples, settled 2026-11-08: 171 exact over all of it) | 44 + 45 + 82 (also 45 + 45 + 81) |
| KM-parent projection-descent 47 (`seeds/projkm47_7`, 2026-11-08: matmul/tomar_line/proj/found47_km56/d180/r47-00007, a fifth class by the rank-triple type alone (a 20/11/16, b 11/27/9, c 20/11/16 factors of rank 1/2/3, no rank 4) and by the exact test; 3 of the 14 47s of the 3 h descent from the Kauers–Moosbauer <4,4,5>:60 projection pool, the other 11 in the KM (5) and projection-descent (6) classes) | 179 | **166**, exact at 2 triples (2026-11-08: scan minimum 167 at 3 of 840 X-cosets, 4493 triples within +4; refine 167 at 32 triples, 168 at 251; settle of those 283: 166 at two, none below; the full window at target 166: nothing below, 166 exact over all 4493 triples and reached by exactly those two) | 44 + 48 + 74 (also 43 + 48 + 75) |

**Slot symmetries in the class stabilizers** (2026-11-09,
tomar_line/proj/stab_slots.py, log tomar_line/proj/logs/stab_slots_five_classes.log;
a slot symmetry is in a class's stabilizer when some sandwich carries the
scheme onto its slot-permuted image).  AlphaEvolve's class and the
projection-descent class: the transpose symmetry (A, B, C) -> (B^T, A^T, C^T)
is in the stabilizer and the certificate sandwich consists of permutation
matrices, so any L program is an R program of the same cost and vice versa
(the published scheme's L = R = 44).  The fifth class: the exchange of the
A and C slots (perm (2,1,0), middle slot transposed) is in the stabilizer,
with a non-permutation certificate; it maps every orbit point with costs
(L, R, Pt) to one with (Pt, R, L), which is why the two 166 points are
mirror images, 44 + 48 + 43 and 43 + 48 + 44.  Kauers–Moosbauer's and
AlphaTensor's classes have no slot symmetry in their stabilizers.  No class
has a symmetry moving the R slot, so no isotropy can transport an L or P
program onto R: the fifth class's R = 48 is its own bottleneck.

(Annealing: all 24 chains per class end at 168 under Boyar–Peralta
scoring; the 167 needs the exact search on one side.)

All three are flip-isolated (no two products share a factor), so plain
flip walks cannot leave them; a rank-47 walk with up-and-down excursions
(`flip 4 4 4 --walk --rank 47`, max excess 2) found nothing new in 5 min.

## Symmetry-prescribed SAT search (2026-11-09): dry

The route that found new 3x3 classes (Burichenko; Ballard–Ikenmeyer–Landsberg–Ryder):
prescribe a symmetry group and solve for the invariant decompositions.  `hcnf.py`
quotients the Brent system of <4,4,4> over F₂ by a group of permutation triples acting
as sandwiches (U → X U Yᵀ, V → Y V Zᵀ, W → X W Zᵀ), one orbit shape at a time (per
conjugacy class of subgroups, a count of orbits whose stabilizer is that subgroup; the
representative's entries are the free variables, identified under the stabilizer), as
CNF with one Tseitin AND per monomial and XOR ladders; `hpool.py` runs cadical/kissat
over the shapes, most full orbits first, and decodes any model with a full
4096-equation check.  Group `d8` = the mod-2 image of the dihedral group of eight
signed permutations in Stab(accurate_262) (X = Z in every element; the 262's 48
products are six free 8-orbits, so a 47 needs 8a + 4b + 2c + d = 47 with small orbits
or fixed products).  Positive control: the standard scheme is eight free orbits; shape
0:8 at rank 64 is SAT in under a second and decodes.

Result: nothing.  The plain pool (12 workers, cap 1200 s, cadical seed 100) ran
09:18–13:33 over the 144 shapes with five or four full orbits: every one timed out,
none decided (symsat_2026-11-09/hpool_d8_plain_pool.log).  Rank 48 with six free
orbits, the 262's own shape, also times out at 1200 s (the 262 itself has no mod-2
reduction: every product's 2-adic valuation sum is negative).

Would satsuma or hydra_satsuma be faster?  No.  `hsym_audit.py c0,...,c7` lists the
quotient's symmetries exactly: for shape (4,0,0,2,0,0,3,1) the permutations of orbits of
the same type (288) times the normalizer of d8 in S₄³ (4 cosets) are all symmetries of
the solution set, but the XOR ladders fix each equation's monomial order by variable id,
so every one that moves a U variable reorders the ladders: a single involution (fixes
U, permutes the columns of V and W) is the whole clause-graph automorphism group.
`tools/cnf_wl_symmetry.py` (colour refinement on the clause graph) confirms it on the
CNF: every class has size 2.  satsuma's dejavu would therefore add one lex-leader
constraint, a factor 2 at most on UNSAT proofs; hydra's XOR stage recovers the 24064
ladder XORs, GE-forces 512 variables, and its cadical reaches no verdict in 1200 s
(symsat_2026-11-09/p1_hydra.out).  The hidden symmetry can be injected instead:
`--lex` adds lex-leader clauses for the consecutive orbit swaps and the normalizer
coset representatives (9 generators, +2% clauses; the rank-64 control stays SAT and
decodes).  Equal-budget pilot, same solver, seed and cap as the pool's round: all eight
lex arms time out, as do rank-48 0:6 plain and lex (lex_pilot_lane.log).  Ten long-cap
arms (12600 s, lex, cadical and kissat; rank-48 0:6 and four rank-47 shapes) ran as the
line's last test, started 13:35; their verdicts are appended below when they land.

Context: Moosbauer–Poole's symmetric flip graphs (arXiv:2502.04514; C₃ and C₃×Z₂ over
F₂ with Hensel lifting; their wins are <5,5,5>:93 and <6,6,6>:153) found no 4x4 scheme
below 49, and our October S₃ slot-symmetry quotient found none at 47 in 8 h.  Two
methods and three groups agree that imposed symmetry costs 4x4 at least two ranks, and
the five known rank-47 classes carry at most an order-2 stabilizer.  Don't build a
symmetric flip mode for 4x4.
