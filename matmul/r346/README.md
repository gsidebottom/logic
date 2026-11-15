# r346 — looking for <3x4x6:53> (2026-11-14)

<3x4x6:53> would be the nearest rank record that beats <3x3x6:40> as a level of the multiplier
(saving 0.736 against 0.741; `../levels/ratio_screen.py`).  The known rank is 54.  Tried:

- **Flip-graph descent over F2** (`flip 3 4 6 --seeds-dir seeds`, 5 threads, 26 minutes): 16,260
  trajectories and 193 million flips from Perminov's ternary schemes of ranks 54, 56 and 57
  (`seeds/`, their images mod 2): not one reduction.
- **k-subset re-solve over F2, exact** (`kres8`: kres.rs with 512-bit Kronecker products, since
  12 x 24 does not fit 256): no rank-53 scheme within 9 products of the 54, and no other 54 either
  (k = 9: 5.3e9 subsets, 16.6 million candidates, all refuted; `results/`).  The 54's span holds
  exactly its own 54 rank-one elements.
- **Continuous descent on the variety** (`../vdescent`, new): the 54 lies in an 8-parameter family
  of inequivalent schemes; 5 runs of 400 steps find no reduction in it.

- **Numerical search** (`vdescend --search`, `--warm`: regularized Levenberg-Marquardt from random
  starts, or from a known scheme less some products): built and validated, but it does not reach
  this size.  It finds <2x2x2:7> from 37 of 40 starts, <2x2x3:11> 32 of 40, <2x3x3:15> 24 of 40,
  <3x3x3:23> 32 of 40 (6 s) and <3x3x4:29> from about 4% of starts, and it rejects the ranks that do
  not exist (<2x2x2:6>, <2x3x3:14>, and <2x2x3:10>, <3x3x3:22>, which it approaches only
  approximately: border rank); but it finds nothing at <3x4x4:38> or <3x3x6:40>, and the warm
  starts do not recover the known 54 from the 56 less two products.  So its one run at 53 (the 54
  less one product: 0 of 20 starts, residuals 0.15-0.60) says nothing (`results/lm_search_validation.txt`).

- **Clamping** (`--sparse`, after Smirnov's practice): each scheme the search finds is slid along
  its orbit under a sparsity penalty while its smallest entries are set to zero and frozen a few at
  a time (undone if the scheme cannot be restored), then normalized on its torus, its nonzero entries
  clamped to +-1, +-1/2, +-2, and the result verified in integers.  It works as a finisher: of the
  schemes found from random starts, 27 of 27 at <2x2x2:7> and 29 of 31 at <2x2x3:11> come out exact
  over Z, 5 of 21 at <2x3x3:15>, 2 of 30 at <3x3x3:23> (the others are 66-76% zeros with entries that
  are not simple).  It does not extend the search's reach, and cannot: clamping needs a scheme to
  clamp, and from <3x4x4:38> up the search does not get near one.  (Putting the sparsity pressure
  inside the search made it worse: <3x3x3:23> from 0-12 of 40 starts against 32.)

- **Other rank-54 schemes** (`schemes/`): AlphaEvolve's and the entry of Sedoglavic's table were on
  disk after all.  Both have the type of Perminov's ternary scheme (18 products each of factor
  ranks (2,2,2), (1,2,1), (1,1,2)) and 8 moduli: one scheme, three writings.  There is no second
  class to start from.
- **Its symmetries** (`sym/autgroup.py`): a group of order 6, S3 -- two elements of order 3 that
  fix no product (the 54 are 18 orbits of three) and three of order 2 that fix two (26 pairs + 2).
- **The search among symmetric schemes** (`vdescend --sym`): a scheme invariant under a group
  element is its orbits' representatives, a third of the unknowns for order 3 (972 of 2916), and
  the equations are invariant too.  Near the known scheme this search has the power the plain one
  lacked: from the 54 with 5%, 20% and 50% noise it returns to an exact 54 every time (18 of 18
  starts; order 2: 4 of 4).  At rank 53 from the known scheme it finds nothing: one orbit dropped
  and two fixed products added, 0 of 144 starts (best residual 0.015); two orbits dropped and five
  added, 0 of 72; order 2, the 26 pairs and one fixed product of each sign type, 0 of 54 (best
  0.16).  From random starts it does not find even the known symmetric 54 (0 of 440), so nothing
  can be said about a 53 away from the known scheme (`results/symmetric_search.txt`).
- **The norm-constrained search proper** (Tichavsky, Phan and Cichocki: minimize |F| inside a
  ball, the multiplier by bisection; `--cnorm`): works, and is no better than the penalty --
  <3x3x3:23> from 30 of 40 starts (penalty: 32), <3x3x4:29> from 0-1 of 80 (penalty: 3-4).

- **A flip graph with a symmetry imposed** (`src/bin/symflip.rs`, over F2): the walk stays among
  the schemes invariant under a group of triples (X, Y, Z), every flip, merge and plus transition
  applied to all images at once; the group is index permutations (`--gen`, from the standard
  scheme) or the start scheme's own symmetries (`--aut`, found by running through GL_3 x GL_4 and
  solving for Z).  Every scheme at a new low is checked against the tensor and the group.
  Checks: <2x2x2> 7 plain and under Z2; <3x3x3> 23 plain and under Z2 (three fixed summands), 24
  under Z3.  **Over F2 the 54 has 18 symmetries**, not 6: nine of order 2 (two fixed summands
  each) and eight of order 3 (none fixed), four subgroups of order 3.  (Not settled: whether the
  real search in `sym/autgroup.py`, which takes X to be a signed permutation, missed twelve, or
  they exist only mod 2.)  No two summands of the 54 share a factor, so every walk from it starts
  with plus transitions; a first campaign whose split move was merged straight back made no flip
  from the 54 and is void (not kept).
  Campaign (`sym/run_symflip.zsh`, `results/symflip_2026-11-14.log`; 3 min and 10 threads an arm):
  - from the standard 72: plain 60; Z3 (rows cyclic, columns two 3-cycles) 60; Z2 x Z2 60; Z6 60;
    the two Z2 63; S3 68.  The symmetric walks make a fifth to a tenth of the plain walk's flips
    and do no better in 3 minutes; none is near 54.
  - from the 54, plus transitions throughout (220-430 M flips an arm): no 53 under no symmetry, a
    Z2, each of the four Z3, the group of order 9, an S3, or all 18.  Two arms reach
    other rank-54 schemes where the plain walk reaches none: one Z3 (5) and the group of order 9
    (19), saved in `sym/found/k54_z3_6`, `k54_33` (`results/symflip_54s_2026-11-14.log`).  All 24
    share no summand with the known scheme and all have its type and 18 symmetries
    (`sym/bits_type.py`, `symflip --aut --list`): what images of it under the group of the tensor
    would look like; equivalence not proved, no second class shown.
  - from the 56 (its own group has order 2): no 55, plain or under the Z2 (1.5-2.9 G flips).

- **The flip graph over F3** (`src/bin/symflip3.rs`, 2026-11-15).  Why: a scheme over Q with odd
  denominators reduces mod 2 and the F2 searches see its image; one that needs halves reduces
  mod 3 instead.  Summands are normalized factor triples with a coefficient +-1, flips take
  lambda = +-1, and with a group (index permutations) every move is an identity old = new summed
  over the group and applied when the left side is a multiple of the scheme's own summands (a
  flip of a summand with its own image doubles the summands and is refused).  Checks: plain
  <2x2x2> 7, <2x2x3> 11, <2x3x3> 15, <3x3x3> 23; symmetric <2x2x2> 7 under Z2, <3x3x3> 24 under
  Z2 and Z3.  Seeds: the known schemes mod 3 (`sym/to_trits.py`, `seeds/*.trits`; DPS's <3x3x6:40>
  has halves and reduces mod 3, not mod 2).  Campaign (`sym/run_symflip3.zsh`,
  `results/symflip3_2026-11-15.log`, 10 threads):
  - <3x4x6> from the 54: no 53 in 8 min (1.4 G flips, 68 M plus transitions) or 5 min with wider
    excursions.  Unlike over F2 the walk leaves the start at once and fills its pool with other
    54s; a sample of 20 all have the known type and share 29-49 of its 54 summands, differing in
    multiples of five: the F3 points of the known 8-parameter family, not another class
    (`sym/trits_type.py`).
  - <3x3x6> from DPS's 40 and from PLinOpt's original 40: no 39 (6 + 4 + 4 min, 1.7 G flips,
    220 M plus transitions), and no other 40 either: the walk always returns to the start, as
    the moduli count 0 says it should.
  - what the walk cannot do: from the 56 and the 57 it finds no <3x4x6> scheme below them, from
    the 42 and the 43 no <3x3x6> below them (1.1-1.6 G flips each), although 54 and 40 exist
    mod 3.  So "no 53" and "no 39" here cover the neighbourhood of the known schemes only.
  - from the standard schemes F3 descends far worse than F2: <3x4x6> plain makes no reduction
    in 2.1 G flips (F2: 60 in 3 min), Z2 x Z2 68, Z6 66, Z3 none; <3x3x6> plain 54 -> 51.  A
    merge needs two factors to coincide, and each normalized factor has 364 values over F3 where
    it has 63 over F2.
  Not done over F3: the 54's own symmetries (GL_3 x GL_4 has 2.7e11 pairs mod 3).

- **The k-subset re-solve in characteristic 0** (`src/bin/kresr.rs`, 2026-11-15).  kres decides over
  F2; a rewrite of k products by k - 1 that needs halves or irrational constants it cannot see.
  kresr asks the same question over Q and R.  Stage 1 is exact: if in some slot the k factors
  are independent and so are the k Kronecker products of the other two slots (ranks mod
  2^61 - 1, which never exceed the ranks over Q), the sum of the k products has rank exactly k
  and the subset is irreducible over any field of characteristic 0.  Stage 2 is a search: the
  sum, compressed to its factor spans, is fitted with k - 1 products by Levenberg-Marquardt from
  warm and random starts (a light pass everywhere, a full one where the light pass comes within
  0.05); a miss leaves the subset open, it is not a proof.  Candidates: kres8's list where the
  scheme is integral (a dependency over Q gives one mod 2), every subset otherwise (`--all`).
  Check: on the standard <2x3x3> scheme it reduces all 72 seven-subsets and all 729 eight-subsets
  that kres finds reducible or leaves open (residuals 1e-14).
  - both <3x3x6:40> schemes (DPS's accurate one and PLinOpt's original, `schemes/3x3x6_m40_*.json`;
    every subset, since their F2 images are degenerate): k = 3, 4, 5 all 759,278 subsets PROVED
    irreducible; k = 6: 48 of 3,838,380 not proved, k = 7: 2,368 of 18,643,560, k = 8: 56,475 of
    76,904,685; none of those reduced, best residuals 0.82 / 0.51 / 0.34 (DPS) against 1e-14 for
    a true reduction.  The two schemes give the same counts, as two points of one orbit must
    (`results/kresr_40dps.log`, `kresr_40orig.log`; 30 and 32 min).
  - <3x4x6:54> (kres8's candidates): k = 5: 9, k = 6: 909, k = 7: 38,358 (36 proved), none
    reduced, best residuals 0.85 / 0.49 / 0.40 (`results/kresr_54_k5-7.log`).  k = 8: all
    963,324 candidates, none reduced, best residual 0.38 (two runs: the first was stopped by its
    time cap after two complete blocks of 200,000 with no reduction printed, `kresr_54_k8_part1.log`;
    the second took the other 563,324: 2,010 proved, 561,314 open, best 0.44, `_part2.log`, 98 min).
  So neither scheme has a local reduction within 8 products over the reals as far as this search
  sees; for the 40 that is a proof up to k = 5 and for all but 0.07% of the subsets up to k = 8.
  For the 54 the exact stage settles little (its dependencies over Q are those over F2), and the
  statement rests on the numerical stage: residuals of 0.4 where a reduction gives 1e-14.

No 53, no 39.  Kauers and Moosbauer's own schemes (arXiv:2306.00882, github.com/jakobmoosbauer/flips) are
on disk in `matmul/perminov_cache/repo/schemes/known/jakobmoosbauer_flips/`: their <3x4x6> is the
rank-56 scheme (`346-56-mod0.m`), not a second 54.
