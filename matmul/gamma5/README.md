# gamma5 — can a 5×5 scheme give a fast and more accurate level than accurate_262?

Question (2026-10-28): the best known ⟨5×5×5⟩ schemes have rank 93, so one 5×5
level saves 93/125 = 0.744 of the products, as much as a ⟨4×4×4:48⟩ level
(0.75).  Could a 5×5:93 level be as fast as our accurate_262 level in the fused-pass
library on the M4 Pro and more accurate?  **No, not with the known 5×5 classes**: the
continuous orbit minima of the better class fall short of accurate_262's
figures when both quantities must hold at one point, before any exact point is
even sought, and a 5×5:93 level measured 2–26% slower than the 4×4 level as one level and
17–22% slower in the planner's best plans, its passes running at half to two thirds of the
4×4 passes' bandwidth.

Schemes (both on disk in the Hell's Bells backup, `matmul/out/scratch_backup_2026-10-22/
hellsbells/repo/algorithms/other/unsorted/misc/`):
- `MoosbauerPooleKemper-555-93-mod0.exp`: the rank-93 scheme of Moosbauer and Poole
  (arXiv:2502.04514, ISSAC 2025; valid over any ring, coefficients ±1), with the cyclic
  symmetry that makes its three roles identical.
- AlphaEvolve's `decomposition_555` in `AlphaEvolveSchemes.py.txt` (from
  google-deepmind/alphaevolve_results, Apache 2.0): also rank 93, coefficients ±1, a
  different class (its orbit minima differ).  Our conversion to PLinOpt programs and
  matrices is in `slp/ae93_{L,R,P}.{slp,sms}` (SLPchecker and MMchecker pass).
- `Adaptive-555-94-mod2.m` (rank 94, valid mod 2 only) is unusable for floating point.

Quantities as in `../gamma3`: γ∞,∞, γ∞,2, γ₂,₂, γ₂, DPS's Q₀, amp (the quantity that
ordered the measured errors of the 4×4 paper).  Exponents are log₅ of the factor, and
log₅(amp/(√5/2)) for amp.

## Accuracy

**Thresholds.** At equal product saving a 4×4 level is 0.973 of a 5×5:93 level, so a
5×5 scheme's excess growth over the classical algorithm, (γ/5)^0.973, must stay under
accurate_262's 22.63/4: **γ∞,2 ≤ 29.7, γ∞,∞ ≤ 182, amp ≤ 3.26** (the exponent-parity
line, 5^2.25 = 37.4, is weaker).

**Representatives** (`screen5.py`, ±1 points, best role):

| scheme | γ∞,∞ | γ∞,2 | γ₂ | Q₀ | amp | nonzeros | direct additions |
|---|---|---|---|---|---|---|---|
| MPK93 | 555 | 112.0 | 709 | 45 | 11.78 | 1224 | 1013 |
| AE93 | 413 | 94.5 | 517 | 42 | 10.16 | 1057 | 846 |
| accurate_262 (4×4) | 132 | 22.63 | 154.5 | 34 | 2.83 | 864 | 752 |
| DPS's ±1-type points of the same 4×4 orbit (sparse, canonical, 201) | 399–516 | 76–98 | 370–427 | 31–44 | 9.5–12.0 | 624–760 | 512–648 |

The 5×5 representatives sit where the 4×4 orbit's ±1 points sit, and DPS's
construction (the orbit's γ₂ minimum, then Hadamard isotropies) took that orbit down
3.4–4.3× in γ∞,2 and amp.  The 5×5 schemes need 3.2–3.8×.

**Orbit minima** (`orbit5.py` → `orbit5_minima.csv`, `.log`: L-BFGS over GL₅³, 75
parameters, 24 starts, every role; the same code reproduces the 4×4 orbit's known
minima from DPS's `accurate` point: γ∞,2 21.41, amp 2.828, γ₂ 154.51, see
`orbit5_run1.csv`):

| class | γ∞,2 min (exp) | amp min (exp) | γ₂ min (exp) | both thresholds at one point (`orbit5b.py`) |
|---|---|---|---|---|
| AE93 | 26.6 (2.038) | 3.160 (0.645) | 295.9 (3.535) | best max(γ∞,2/29.7, amp/3.26) = **1.042** |
| MPK93 | 35.5 (2.218) | 3.795 (0.759) | 349.8 (3.639) | 1.326 |
| accurate_262's orbit | 21.41 (2.197) | 2.828 (0.750) | 154.51 (3.636) | (the exact point is 5.7% above the γ∞,2 minimum and at the amp minimum) |

AE93's class passes each threshold separately (by 10% on γ∞,2 and 3% on amp) but at
different points: at its γ∞,2 minimum amp is 4.38, at its amp minimum γ∞,2 is 47.7, and
the best compromise is 4–5% above both thresholds.  MPK93's class misses both.  Every
minimizer is a dense irrational point (1400–2320 of 2325 entries nonzero per factor,
3300–4900 distinct coefficients), so an exact point would sit above these floors, as
accurate_262 sits above its orbit's γ∞,2 floor.  The Hadamard route is open in five
dimensions (unlike three): 352 unordered sets of mutually orthogonal rows at
denominator 2 (the ⟨0,1,1,1,1⟩/2 and unit rows) and 2912 at denominator 4 (adding
⟨3,2,1,1,1⟩/4), against 32 signed permutations, but the continuous floors already
decide the question.

## Speed

The fused-pass cost model (`../gamma3/cost3.py` constants, n = 8192 f32): one 4×4
level 16.8% off the GEMM, one 5×5:93 level 15.9% (118 blocks of n/5 moved per level
against 64 of n/4: 18% more pass traffic for the same saving); at 16384 and above the
two are equal within the model (20.7–24.4%), and two 5×5 levels lose to two 4×4
levels (21.7% against 27.3% at 16384).  A 5×5:96, 97 or 100 level saves 13.2%, 12.4%
and 9.7%.

**Measured** (`../fastmm/results/fmm93_speed_2026-10-28.txt`): the AlphaEvolve scheme's
direct-sum programs as fused kernels in a copy of the library whose D48 slot has grid 5 and
rank 93 (`lv_grid`, `lv_rank`; the error model's size N_E moved from 2048, which 5 does not
divide, to 6400; the block and product pointer tables widened to 32 and 128:
`fastmm93.patch`), calibrated on its own, against the real library at the same sizes, five
interleaved reps each, minimum times; L+R+P are the three passes' times:

| n, type | plan | 5×5:93 | 4×4:48 (accurate_262) | 5×5 passes | 4×4 passes |
|---|---|---|---|---|---|
| 5120 f32 | D48/G | 0.088 s (0.94× the GEMM) | 0.070 s (1.33×) | 0.015 s | 0.009 s |
| 5120 f32 | auto | 0.075 s, SW+2/SW/G3 (no 5×5 level) | 0.064 s, SW+4/D48/G6 | | |
| 10240 f32 | D48/G | 0.556 s | 0.543 s | 0.071 s | 0.039 s |
| 10240 f32 | SW/D48/G | 0.641 s | 0.513 s | 0.132 s | 0.093 s |
| 10240 f32 | auto | 0.507 s, D48/G3 | 0.417 s, D48+4/D48/G6 | | |
| 5120 f64 | D48/G | 0.285 s | 0.265 s | 0.039 s | 0.020 s |
| 10240 f64 | D48/G | 2.166 s | 2.058 s | 0.179 s | 0.078 s |
| 10240 f64 | SW/D48/G | 2.046 s | 1.912 s | 0.313 s | 0.184 s |
| 10240 f64 | auto | (not calibrated) | 1.539 s, SW/D48+4/D48/G6 | | |

The 5×5 level's GEMM part is as cheap as the 4×4 level's (0.495 s against 0.510 s at
10240 f32: 93 products of 2048 against 48 of 2560), but its passes take 1.7–2.3× longer
for 1.18× the traffic: 118 streams per pass run at 50–70% of the bandwidth of the
64-stream passes the library was tuned for.  As one level the 5×5 is 2–5% slower at
10240 and 8–26% slower at 5120; the planner's best plan is 17–22% slower, and at 5120
f32 it avoids the 5×5 level altogether.  Grouping the 93-stream passes might recover part
of the bandwidth, but that only chases parity, and the accuracy side is already lost.

## Files

- `screen5.py exp|ae|sms ...`: growth factors of a square scheme in all roles (`.exp`
  one product per line, AlphaEvolve's python factor matrices, PLinOpt `.sms`); run with
  `python3 -I` (it adds numpy's user site itself).
- `orbit5.py OUT.csv SPEC...`: orbit minima of γ∞,2, amp, γ₂; `orbit5b.py`: the same
  with the joint objective (`KINDS=joint TG=29.7 TA=3.26`).
- `mk_slp.py SPEC PREFIX`: a scheme as PLinOpt `.slp` direct-sum programs and `.sms`
  matrices (`slp/ae93_*`).
- `orbit5_run1.csv` (8 starts, with the 4×4 calibration), `orbit5_minima.csv`/`.log`
  (24 starts), `orbit5_joint.csv`/`.log`.
- The speed measurement: a copy of `../fastmm` with the D48 slot's grid set to 5 and
  rank to 93 (`lv_grid`, `lv_rank` in `fmm.c`) and kernels generated from
  `slp/ae93` (`gen_kernels.py build/kernels.h --dps48 slp/ae93`); results in
  `../fastmm/results/fmm93_speed_2026-10-28.txt`.
