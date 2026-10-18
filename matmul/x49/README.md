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

## Results (2026-10-18): no point below 156 found

- **Strassen² class** (`ref/` mod 2 = `f2/s49`): the exhaustive orbit
  scan (one Boyar–Peralta run per side) gives minimum 156
  (`scan49.log`).  All 1291 coset triples within 2 of it were refined
  exactly (`refine49.log`): 36 reach 156, the rest 158, and
  Boyar–Peralta was optimal on every side.  A point below 156 would
  need exact costs at least 4 below the scan's on a triple outside that
  window; `xor47 settle` (as used in `../x47/`) could rule this out but
  has not been run.
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
```

`screen` reads a list of `.bits` paths and runs CHAINS annealing chains
of STEPS steps per scheme from random orbit points.  `scan` and
`refine` are described in `../x47/README.md`.
