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
- `geometry.py`, `frames.py`, `perfect.py`, `td/quartic*.py`, `td/acc.py`, `td/outs.py`: the F4 frames and symmetric points.
- `canon_enum.py`, `canon_classes.py`, `unit_lines.py`, `td/tri.py`, `td/t66.py`: exact canonical counts over the orbit.
- `pclasses.py`, `pside.py`, `td/pdeep.py`: the P map.  `vlines.py`, `run_vl.sh`: every line-fixed V at the record P.
- `seeded262.py`, `td/score76.py`: the 76-operation R programs of accurate_262.

