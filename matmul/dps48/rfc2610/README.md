# Sedoglavic's RFC 2610 (received 2026-10-30): checks and experiments

The note, its `4x4x4_48_203_{L,R,P}` files and `slp2matsprod.py` are his and are not committed here.
Scripts take the directory holding those files and PLinOpt's `data/` as arguments; `run*.sh` hold
this session's scratchpad paths.  `results.txt`, `run.out` and `run_resc.out` are the raw output.

| point | L | R | P | total | canonical L, R | amp |
|---|---|---|---|---|---|---|
| Joshua's 204 | 57 | 57 | 90 | 204 | 10, 10 | 10.44 |
| his 203 (Joshua's L, R, our P) | 57 | 57 | 89 | 203 | 10, 10 | 10.44 |
| Ruchit's 202 | 56 | 56 | 90 | 202 | 8, 8 | 10.26 |
| our lam01c0_201 (the note's "Greg"; October 21) | 56 | 56 | 89 | 201 | 8, 8 | 10.26 |
| our 201 in PLinOpt (p005) | 55 | 57 | 89 | 201 | 6, 4 | 9.53 |
| DPS accurate_262 (the library's) | | | | 262 | 0, 8 | 2.83 |

`../cand48/lam01c0_201_*` matches the point (4) produces on all 48 products exactly (`lam01c0.py`): it is
a signed permutation of Ruchit's point, and it is what the note calls Greg's decomposition.

**Verified from the files alone** (`verify_note*.py`; every action gated on fixing the tensor):
- The 203 circuit: 4096 Brent equations, SLPchecker on all three programs, ten canonical L and R rows.
- (1) on the rational point and (3) on the 204 point, exactly, by Lemma 2.1 as written; (1) gives
  canonical rows (10, 10, 10).
- (9) fixes the (1) point, (10) the 204 point, (11), g2, g13, g14 the point (4) produces, with
  permutations exactly pi2, pi3, pi4; {1, pi2, pi3, pi4} is a Klein four-group.
- The numbering of the k in `∘ k` is not needed: all six elements tried, ∘3 is the input swap, ∘5 a
  rotation, ∘6 a swap after a rotation.
- The same six on his own [L; R; P] (`s3_lrp.py`, 2026-10-31), with K the commutation matrix: ∘3 = [R K; L K; K P]
  swaps L and R, ∘5 = [R; Pᵀ K; K Lᵀ] rotates, ∘6 = [L K; Pᵀ; Rᵀ] swaps R and P.  Each printed use is reproduced by
  exactly one of the six, 48 of 48 products against at most 1, and only with the isotropy acting after the map.
  The other two are [Pᵀ K; L; K Rᵀ] and [Pᵀ; R K; Lᵀ]; which is ∘2 and which ∘4 is his to say.

**To correct in the note:**
- rho is printed as (3)(4); Lemma 2.1 needs (4)(3), V = [[0,0,1,0],[0,-1,1,0],[1,0,0,0],[0,0,0,1]]: 48
  of 48 products against 6 of 48.  V does not touch P, so the 203 result is unaffected.
- Section 3's 56 for Joshua's L and R should be 57; 56 is Ruchit's and lam01c0_201's.  The 56 + 56 + 89
  before (5) is right: it is lam01c0_201.
- The last sentence's second pi3 should be pi4 (pi3(8) = 29, pi4(8) = 1).

**Checked earlier:** the stabilizer's order 64 and its 32 + 32 split, on lam01c0, 2026-10-24
(`../stabilizer48.py`, plan doc).  **Not checked:** `slp2matsprod.py` (not run).

**Search on the 203 point:** lns48, 12 seeds x 180 s: L and R 57 in 48 of 48 runs, naive or seeded.
Six product rescalings, all exact: the 16 half-carrying products give 226, 226, 238, product 43 alone
204 three times (its halved signal is reused four times, so the halving stays); control P 89.
Heuristic over 2 of the 65,536 subsets, not a lower bound.  His point maps to our published 201 with
all 48 product scalars exactly +-1 (`derive.py`), so his footnote's sign change is exact.

**V-only search with P fixed at 89** (`run_vonly.sh`, 10.3 thread hours): 180 points from four starts, P unchanged
on all of them.  L + R stops at 112, at 38 points, as 55 + 57, 56 + 56 and 57 + 55; a 200 would need 111.
Controls: 112, 112, 112 and 114 on the four known points.

**The stabilizer on the 89-operation P program** (`symtest.py`; exact; every element gated on A P = P M).  A form
counts as kept if the element sends it to a form of the same program.

| | P program, 44 internal forms | P^T program, 19 internal forms | outputs onto outputs |
|---|---|---|---|
| g2, g13, g14 | 0, 0, 0 | 8, 5, 5 | 8 of 16 each |
| best of all 63 elements | 8 | 11 | 16 of 16 |
| 200 random signed permutations, max | 6 | 2 | |

The transposed program is the cleaner test, with one operation per line; the direct one has multi-term lines
whose partial sums are not compared.  It is partly symmetric, far from invariant.  Positive control: at the 203
point R's 55 forms map onto L's completely, random at most 2.  Our own L and R at lam01c0_201, found by
independent runs, are related on 47 of 54 forms.

## Follow-up, 2026-10-31

His reply asked about invariant circuits and the 10,10,728 family.  Raw output: `results_td_2026-10-31.txt`; the summary is
the 2026-10-31 paragraph in doc/matmul_plan.md.  His 160 decompositions are not committed; the scripts take paths.

- `run_td.sh`, `td/score.py`: the sweep of his 160 points.
- `stab_matrices.py`, `gamma_fixed.py`: the stabilizer with its matrices; orthogonality and the gamma_2 minimum.
- `invcirc.py`: which programs are invariant, per side.
- `lbfacts.py CAND48_DIR`: orbit invariants of the 201 record for judging lower-bound methods (lines, ranks, collinear triples, dependent 4-sets, additions and scalings).
- `geometry.py`, `frames.py`, `perfect.py`, `td/quartic*.py`, `td/acc.py`, `td/outs.py`: the F4 frames and symmetric points.
- `canon_enum.py`, `canon_classes.py`, `unit_lines.py`, `td/tri.py`, `td/t66.py`: exact canonical counts over the orbit.
- `pclasses.py`, `pside.py`, `td/pdeep.py`: the P map.  `vlines.py`, `run_vl.sh`: every line-fixed V at the record P.
- `seeded262.py`, `td/score76.py`: the 76-operation R programs of accurate_262.

## His Gram-matrix remark, 2026-11-09

His 2026-11-08 reply: the [1,1,1] vectors lie on the unit sphere of R^4 and, by their Gram matrix, the same group should
act on them in every mode.  `gram_modes.py` (output `results_gram_2026-11-09.txt`): at accurate_262 each mode's sixteen
lines (four of the six F4 frames, frames.py) have the same multiset of absolute inner products, 56 zeros, 32 of 1/sqrt2 and
32 of 1/2, and W(F4) (order 1152, generated by the signed permutations and the Hadamard frame) holds 128 isometries
carrying any mode's lines onto any other's.  So the three configurations are congruent, as he expected, and the
configuration's own symmetry group has order 128 where the scheme's trivial-slot stabilizer acts per mode by 32 elements;
the extra configuration symmetries are not isotropies of the decomposition (the stabilizer is complete at 64), so they do
not answer his question 1 either.

## Isotropies between the DPS points, 2026-11-01

He lost the isotropy from the original 315 (`4x4x4_48_rational`) to accurate_262, so he cannot conjugate the known stabilizer onto it.

- `iso_between.py SRC TGT OUT.json`: every isotropy between two points, exact, written as a map on [L; R; P], then Lemma 2.1 with primitive integer
  U, V, W.  Run on rational -> 262, rational -> accurate, accurate -> 262, rational -> rational and 262 -> 262, about a minute each.
- `iso_gate.py DATA WORK REPORT`: gates from the raw .sms, independent of the transport; his recipe g s g^-1; orthogonality of accurate -> 262; the
  signed-permutation subgroup; the text for him.  Output: `results_iso_2026-11-01.txt`.

g = (U x V x W)∘5, entries 0, ±1.  Stab(315) -> Stab(262) by conjugation, 64 of 64, one to one.  Signed permutations in all three modes: 315 4,
accurate 4, 262 8, 204 2, lam01c0_201 1.  The 8 at 262 are dihedral of order 8, all with trivial slot map; the two of order 4 have cycle type 4^12.

## Turning a scheme, 2026-11-01

He wrote that the gamma_inf,2 search should be redone after a first turn that suits the stabilizer, because the accuracy points never had it.  They did:
Stab(315) swaps R and P, Stab(accurate) and Stab(262) swap L and R, and all 64 isotropies from the 315 send its L mode to the P of 262.  His note's turn is (2),
Id x Id x Id ∘5; ∘3 alone is the input swap, which changes no gamma_{p,q}.

- `turns.py DATA NAME...`: every growth factor and the amplification in all six orientations, from the raw .sms, independent of gamma48.
- `turned.py SMS_PREFIX SLP_PREFIX OUT_PREFIX`: the two turned forms with their programs, by transposition.  Output: `results_turns_2026-11-01.txt`.

| | γ∞,∞ | γ∞,₂ | γ₂,∞ | γ₂,₂ | γ₂ | amp | ops |
|---|---|---|---|---|---|---|---|
| accurate_262 | 132 | 22.63 | 496.5 | 90.51 | 154.51 | 2.83 | 262 |
| turned ∘5 | 172 | 28.14 | 531.9 | 91.09 | 154.51 | 3.32 | 262 |
| turned ∘6 | 152 | 28.14 | 508.5 | 96.54 | 154.51 | 3.32 | 262 |

The published role is best on every factor.  Measured turned / published (altsim.py, f32, n = 1024 and 4096): means 1.22-1.32, 1.37-1.39, 1.54-1.60 at 1-3 levels; the amplification
predicts 1.17, 1.38, 1.61.  The 260 behaves the same, and its programs compute the published matrices, so its growth factors are the published ones.

His proposal was already run on Oct 25: `gamma48` on rational in role 1 starts at the 315 turned by (2) (39.2820, `../gamma/rs_scale.log`), 2,400 starts, 22.6274 x49 and nothing lower.
gamma_inf,2 is the only whole-orbit objective we have searched.

## 2026-11-09: his questions 1 and 3 on the <4x4x4:48> stabilizer

**Question 1, does he miss an isotropy?**  No.  `stabilizer48.py` (and `stab_matrices.py` on top of it) is exhaustive: for
each of the six slot maps it enumerates every bijection of the 48 layers consistent with the isotropy invariants (the
rank triple of each layer and, for each pair, the ranks of the side-by-side and stacked concatenations in every factor,
refined six rounds), solves X, Y, Z exactly for each, and keeps those whose image is the point layer by layer.  On
accurate_262 (PLinOpt data/4x4x4_48_accurate_262, `stab_accurate_262.json`): order 64, 32 with trivial slot map and 32
carrying L onto R (`cyc2+rev`), all 64 orthogonal up to scale, 8 signed permutations in all three modes (the dihedral
group of order 8), per mode signed permutations in 32 (X), 16 (Y), 32 (Z).  Same numbers as 2026-11-01.

**Question 3, the invariant subspaces of R^4** (`q3_invariant.py PREFIX STAB.json`, `q3_reps.py STAB.json`,
`results_q3_2026-11-09.txt`).  Per mode the commutant of the 32 trivial-slot matrices has dimension 2, spanned by I and
an involution K: in modes X and Z the permutation (1 2)(3 4) of the coordinates, in mode Y the same with two signs.  R^4
splits exactly over Q into the two planes K = +1 and K = -1 (the sum and difference planes), and the two planes carry
INEQUIVALENT representations of the group (characters differ), so there is no canonical identification R^4 = R^2 (x) R^2
and "doubling" has no intrinsic meaning.  In the adapted basis every factor of every one of the 48 terms has all four
2x2 blocks nonzero (the [1,1,1] vectors sit at 45 degrees to both planes, as `geometry.py` found), and only 8 factors
per side are Kronecker products of 2x2 matrices, no term in all three.  So the invariant decomposition does not exhibit
accurate_262 as derived from a smaller tensor decomposition in the way 1703.08298 derives Laderman from Strassen; the
scheme is maximally mixed with respect to its own symmetry planes.  Same picture at the `accurate` point.

**Question 2, does the family behave the same?**  The rank structure does (`../q48_structure.py`, `../q48_structure_2026-11-09.txt`):
every rank-48 scheme we hold has 32 terms of type [1,1,1] and 16 of type [2,2,2], Agrawal's excepted in the 16 (4 x [2,2,2],
8 x [2,2,3], 4 x [2,3,3]).  The stabilizer does not (`../stabilizer48.py`, `results_stab_family_2026-11-09.txt`): the Li-Wang-Hu
points s(1), s(2), s(1/2) have order 32 (16 with trivial slot map, 16 with the slot map `cyc+rev` in that file's orientation), no
signed-permutation element of order 4 and nothing carrying L onto R; Agrawal's has order 8 (4 + 4).  The order 64 with its 32 + 32
split is special to the DPS class (rational, accurate, accurate_262, and the 201 points, checked 2026-10-24).
