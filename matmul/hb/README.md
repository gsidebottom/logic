# hb — sweep of the Hell's Bells 3×3 dataset for fewer additions

Source: E. Mårtensson et al., *Hell's Bells: A Neural Network Pipeline for
Ternary Fast Matrix Multiplication Algorithms*, IACR ePrint 2026/1688;
data in github.com/werekorren/fmm_add_reduction, `algorithms/hells_bells/333`:
15,316 rank-23 schemes for 3×3 with coefficients in {−1, 0, 1}, naive
addition counts 84–145 (mode 92).  The paper's best 3×3 count is 59 and it
states that neither local search nor stronger addition reduction was
applied to this set.  Records to beat: 51 additions per step with a square
change of basis (Stapleton–Perminov; our `external/ks51` class ties it)
and 55 without (our `external/i19` class, Karunaratne–Idamekorala).

## Result (2026-10-19): no improvement in this dataset

| question | method | outcome |
|---|---|---|
| ≤ 50 with basis change (or a new 51) | exact free-basis leg minima (`fbmin`), 564 new classes with floor ≤ 51 | **none reaches 51**; every class ruled out (375 s) |
| ≤ 54 without basis change | whole-orbit lower bound (`hbflat.py`), all 1,736 new classes | **none can go below 55**; 35 classes have bound exactly 55 (possible ties, unverified) |

Controls through the same code paths: our 51 class comes out
`legs 12/13/12 → TIE-51` (as in the original sweep), and the class holding
our 55 gets a flat bound of exactly 55, met by one coset triple.
Cross-check of the flat bound on the lowest-floor new class (class0160,
bound 56): the exact orbit scan (`../orbitscan.py`, all six slot
variants, 51 min) finds an orbit-wide GF(2) input-side minimum of 29–31,
best estimated total 61 and no point at or below 56, consistent with the
bound.

## Pipeline

1. `hbconvert.py DATADIR OUT`: parses the three 9×23 blocks per file,
   tries the entry conventions and keeps the one satisfying all 729
   integer Brent equations (row-major for all blocks; all 15,316 pass),
   writes 621-bit brent-order bits plus the d-profile floors
   (`floor2 = dA + dB + dC − 13`, ../dprofile.py).  Naive counts match the
   filenames exactly.
2. `hbnovelty.py`: fingerprints the six slot variants of each scheme
   against the 17,376-scheme HKS database (../dbcache, ../dbcheck.py),
   exact `equivalent()` on collisions, then exact clustering of the new
   schemes.  8,977 schemes are equivalent to database schemes (997 DB
   classes), 6,339 are new in 1,736 classes.  All 480 floor-47 schemes
   are database classes, already swept (no 50 anywhere in the DB).
   New classes by floor: 48: 11, 49: 63, 50: 178, 51: 312, 52: 474,
   53: 499, 54: 178, 55: 19, 56: 2.
3. `hblegs.py`: one representative per new class with floor ≤ 51;
   `fbmin` tier 1 on every leg, then tiers 2 and 3 only while a total of
   51 is still possible.  A class costs `legs + 14` per step, so ≤ 50
   needs leg minima summing to ≤ 36.  Results in
   `results/legscreen_floor_le51.csv`: all 564 `ruled-out-51`; the proved
   totals are ≥ 52 (75 classes), ≥ 53 (216), ≥ 54 (273).
4. `hbflat.py`: whole-orbit lower bound on the flat count.  Per leg and
   coset pair: distinct non-unit rows, plus one when the inputs' closure
   misses a target; the output leg counts transposed (+14).  Each of
   P, Q, R acts only through its left coset of the 6 permutation matrices
   (28 cosets), so three 28×28 tables and a min-plus over 28³ triples
   cover the whole de Groote orbit; one slot variant suffices since the
   total is symmetric in the legs.  A random-element gate checks the coset
   invariance before the tables are trusted (it caught a right/left coset
   mistake in the first version).  Results in `results/hbflat.csv`: bounds
   55: 35, 56: 82, 57: 186, 58: 362, 59: 494, 60: 357, 61: 165, 62: 42,
   63: 11, 64: 2; about 0.5 s per class.

`out/` (bits, verdicts, legs, logs) is gitignored and regenerable; the
dataset itself is fetched with a sparse clone of the repository.

## Overlap with our own finds

`hbours.py` indexes every 3×3 rank-23 scheme we found ourselves (201,701
files under `../found`, `../new23`, `../found23flip`, `../found23mint`,
`../found55`, `../external`; 24,512 distinct fingerprints; each
Brent-checked on load) and tests the 1,736 new Hell's Bells classes
against them: **601 coincide with a scheme of ours** (539 in the
flip-walk corpus, 56 in the mint corpus, 6 in `found/`), **1,135 do not**.
By floor (matched / new classes): 48: 10/11, 49: 37/63, 50: 83/178,
51: 124/312, 52: 145/474, 53: 152/499, 54: 46/178, 55: 4/19, 56: 0/2.
So about a third of what the neural generator produces outside the HKS
database is reachable by flip walks from it; the other two thirds are
new to everything we have.  None of this changes the verdict: the leg
screen and the flat bound covered all 1,736 classes regardless.
Results in `results/overlap_with_our_finds.csv`.

## Open

- The 35 classes with flat bound 55 could tie the record; deciding them
  needs the exact orbit scan (`../orbitscan.py`, about an hour per class
  with its 168×168 exact tables, or far less with the coset reduction).
- The dataset's remaining 1,172 new classes with floor ≥ 52 cannot beat
  51 by the floor alone (a class costs at least its floor per step).
