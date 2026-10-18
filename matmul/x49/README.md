# x49 — additions for rank-49 ⟨4×4×4⟩ schemes over all rings

Goal: a rank-49 scheme for 4×4 matrix multiplication, valid over every
ring, whose linear maps cost fewer than **156 operations** (leading
constant 5+8/11), the best known count (PLinOpt `data/4x4x4_49_156`,
cited by arXiv:2609.12027; copy in `ref/`).

Reducing a signed program mod 2 never raises its cost, so the F₂ XOR
count of a scheme's mod-2 image is a lower bound for its programs over
the integers.  An F₂ orbit minimum of at least 156 therefore rules a
class out.  Costs are XOR(L) + XOR(R) + XOR(Pᵀ) + 33 (transposition
principle, rank 49), all computed with `../../src/bin/xor47.rs`.

## Results (2026-10-18): Strassen² class proved; nothing below 156 elsewhere

- **Strassen² class** (`ref/` mod 2 = `f2/s49`): **proved that no point
  of its orbit costs fewer than 156 XORs over F₂.**  So no scheme whose
  reduction mod 2 lies in this orbit beats 156 over any ring, without a
  change of basis.  `xor47 lbscan f2/s49 --target 156` bounds every
  side from below by its number of distinct non-unit targets, plus one
  when the inputs' closure misses a target (some gate must then compute
  a non-target), and checks all 840³ coset triples.  In `lbcheck.py`'s
  count, 22,284 triples have target counts summing to at most 123; the
  closure term lifts all but 36 of them past 123, and those 36 are
  exactly the 156 points found by the orbit scan and exact refinement
  (`scan49.log`, `refine49.log`: 36 at 156 among the 1291 triples
  within 2 of the scan minimum).  `lbcheck.py` is written separately
  (its own group enumeration, coset representatives and closure, plus
  self-checks of the action and of the coset tables) and agrees.  Both
  tools fail, as they must, at target 157 (`lb49_*.log`, `lbcheck_*.log`).
- **July F₂ corpus** (flip-graph schemes in the gitignored
  `../found4r/`): the screen covered 36 of 2012 schemes before it was
  stopped (`screen/wave1.*`).  Best 156 (r49-20127) and 157
  (r49-03767).  The five corpus schemes tried with `../lift.py`
  (r49-00001, -00201, -00401, -00601, -06601) do not lift to ±1
  coefficients (sign-SAT UNSAT), so the corpus only counts over F₂.
- **Mixed-inner Strassen family** (`mixed.py`): an outer 2×2 rank-7
  scheme on 2×2 blocks, where each of its seven products gets its own
  inner scheme.  Outer and inner schemes are drawn from Strassen's
  36-element F₂ orbit, so every member lifts to the integers (examples
  in `lift/`).  200 random members (`mix/`; BP cost as constructed
  159–175, `mix_natural.txt`).  `xor47 screen` histogram: 156: 1,
  157: 22, 158: 82, 159: 79, 160: 13, 161: 3 (`screen/mix1*`).
  For the top five, exhaustive orbit scans plus exact refinement of
  each scan's +2 window (`scan_top.sh` → `scan_top.log`): mix-00084
  156; mix-00002, -00009, -00029, -00037 157, with no open sides.

## Files

- `mixed.py`: generates mixed-inner schemes (`mixed.py orbit` counts
  the inner choices; `mixed.py random N OUTDIR [SEED]` writes N
  Brent-checked `.bits` files, default seed 1).
- `pairinv.py`: pairwise class invariant, i.e. the multiset of ranks of
  Uᵢ+Uⱼ, Vᵢ+Vⱼ, Wᵢ+Wⱼ over product pairs, minimized over slot
  permutations.  Different values mean inequivalent schemes.
- `scan_top.sh`: orbit scan and exact refinement for the top five
  mixed schemes.
- `lbcheck.py`: independent check of an `lbscan` lower bound (target
  counts plus the closure term over all coset triples).
- `ref/`: PLinOpt's signed 156 scheme and programs.  `f2/`: mod-2
  SMS inputs for the scans (`s49` and the five mixed schemes).
- `lift/`: sign-SAT lifts to {−1, 0, 1} of mix-00000..00002 and of
  s4_4801 (the S3-quotient SAT scheme, `../x47/out/s3/`).
- `screen/`: `xor47 screen` runs: `calib` (calibration list), `wave1`
  (July corpus, partial), `mix1` (the 200 mixed schemes;
  `mix1_ranked.txt` is sorted by best total).

`out/`, `mix/`, `mixsms/` and `sample/` are gitignored and regenerable.
`mix/` is reproduced bit for bit by `python3 mixed.py random 200 mix`.

## Commands

```
python3 mixed.py random 200 mix
../../target/release/xor47 screen LIST --runs STEPS --depth CHAINS --threads 12 --out RANKED.txt
sh scan_top.sh
../../target/release/xor47 lbscan f2/s49 --target 156 --depth 8 --cap 600 --threads 12 --out out/lb49/t156
../../.venv/bin/python lbcheck.py f2/s49 156
```

`screen` reads a list of `.bits` paths and runs CHAINS annealing chains
of STEPS steps per scheme from random orbit points.  `lbscan` proves a
lower bound on every coset pair: target count, the closure test, then
the exact helper search one level at a time, only for target sets in a
triple that could still fall below the target.  It ends with PROVED or
with the triples left, split into genuine points (all three sides
exact) and open ones (a side beyond `--depth` or `--cap`).  For the
Strassen² class it needs no search beyond the closure test (1 s).
`scan` and `refine` are described in `../x47/README.md`.
