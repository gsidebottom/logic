# levels — piecing a recursion together from square and rectangular sub-schemes

Question (2026-10-28): can a fast and accurate multiplication be assembled from the
best-fitting combination of sub-schemes, square and rectangular, rather than from one
square scheme?  In the fused-pass library a plan is already such a combination: every
level is one scheme applied to the current (M, K, N) sub-problem, the leaf is a GEMM, and
a rectangular level simply hands rectangular sub-problems down.  So the question is which
levels are worth having in the menu.  `levels.py` scores every scheme on disk by the
quantities that decide a fused level's cost and error, any shape; `cost_rect.py` prices
plans that mix them; `orbit_rect.py` finds a class's orbit minima under GL_g1 × GL_g2 ×
GL_g3.

Per level ⟨g1×g2×g3 : r⟩ (`levels.py`, `levels.csv`, 70 schemes):

- **saving** r/(g1 g2 g3), the products kept (0.75 for ⟨4×4×4:48⟩);
- **streams** g1g2 + r, g2g3 + r, g1g3 + r, the blocks a pass reads and writes (64/64/64 for
  4×4:48; the 5×5 measurement showed 118 streams running at 50–70% of the bandwidth, so
  staying at or under about 64 is a constraint, not a preference);
- **traffic** 3 + r(1/(g1g2) + 1/(g2g3) + 1/(g1g3)), pass words per level in units of n²
  on a square problem (12 for 4×4:48);
- **amp** and **γ∞,2**, normalized by the classical algorithm of the shape (amp by ½√g2,
  γ∞,2 by g2) and raised to ln 0.75 / ln saving: the growth per 4×4:48-level worth of
  saving, directly comparable with accurate_262's 2.828 and 5.657 (`amp_eq`, `g_eq`).

## What the menu offers

| level | saving | streams | traffic | amp_eq | g_eq | note |
|---|---|---|---|---|---|---|
| **⟨3×3×6:40⟩ DPS-accurate** (and 6×3×3) | **0.741** | 49/58/58 | **11.89** | **2.280** | 6.162 | beats 4×4:48 on every count but g_eq |
| ⟨3×6×3:40⟩ DPS-accurate | 0.741 | 58/58/49 | 11.89 | 2.453 | **5.125** | the third orientation |
| ⟨4×4×4:48⟩ accurate_262 | 0.750 | 64/64/64 | 12.00 | 2.828 | 5.657 | the library's level |
| ⟨3×4×6:54⟩ AlphaEvolve | 0.750 | 66/78/72 | 12.75 | 4.637 | 6.784 | ±1 point; an accurate point unknown |
| ⟨3×4×7:63⟩ rational | 0.750 | 75/91/84 | 13.50 | 5.734 | 11.13 | |
| ⟨5×5×5:93⟩ AlphaEvolve | 0.744 | 118/118/118 | 14.16 | 8.560 | 17.46 | passes at half bandwidth (../gamma5) |
| ⟨5×5×6:110⟩ Kemper | 0.733 | 135/140/140 | 14.73 | 10.38 | 22.9 | |
| ⟨6×6×6:153⟩ Moosbauer–Poole | 0.708 | 189/189/189 | 15.75 | 9.229 | 18.3 | |
| ⟨2×4×5:32⟩ AlphaEvolve | 0.800 | 40/52/42 | 11.80 | 4.962 | 10.95 | |
| ⟨2×2×2:7⟩ DPS-accurate | 0.875 | 11/11/11 | 8.25 | 3.855 | 10.53 | coefficients in Q(√3) |
| ⟨2×2×2:7⟩ Strassen / Winograd | 0.875 | 11/11/11 | 8.25 | 6.890 / 10.66 | 14.1 / 19.8 | the library's SW |
| ⟨3×3×3:23⟩ (best of JS, AlphaEvolve, 55, 58) | 0.852 | 32/32/32 | 10.67 | 12.7 | 34.1 | |

Everything larger than 4×4 (the Kauers–Wood and Kemper 4×5×6 … 6×6×7 schemes, the 5×5s,
the 6×6) saves more products per level but needs 110–225 streams per pass and, at its
published points, has 8–100× the classical amplification per 4×4-equivalent saving.
Kronecker products add nothing: the composite of two schemes has the per-saving
amplification of its pieces (3×3×6 ⊗ 3×3×6 keeps amp_eq 2.280, DPS-accurate 2×2 squared
keeps 3.855) and the stream count of the product, so a product scheme is never better than
the two levels run one after the other, and the stream explosion makes it worse.

**The one combination that wins on paper is DPS's accurate ⟨3×3×6:40⟩ cycled through its
three orientations.**  Applied to a square problem, ⟨3×3×6⟩ hands down (n/3, n/3, n/6)
sub-problems, ⟨3×6×3⟩ on those gives (n/9, n/18, n/18), and ⟨6×3×3⟩ returns to the square
(n/54)³, so a three-level cycle is a square recursion dividing by 54 (three 4×4 levels
divide by 64).  Per level it keeps 0.741 of the products against 0.75, moves 11.89 n²
words against 12, stays within 58 streams, and its amplification per 4×4-equivalent saving
is 2.28–2.45 against 2.83 (19% less for two of the three orientations) at the points DPS
published, with γ∞,2 9% worse for two orientations and 9% better for the third.

## Cost model (`cost_rect.py`, n = 8192 f32, no stream penalty)

| plan | saving vs GEMM | plan | saving vs GEMM |
|---|---|---|---|
| D48/G | +16.8% | 336/G | +17.8% |
| D48/D48/G | +10.8% | 336/363/G | +13.9% |
| SW/D48/G | +14.3% | SW/336/G | +15.3% |
| D48/D48/D48/G | −49.2% | 336/363/633/G | −33.9% |
| 346/G | +16.3% | 555/G | +15.9% |

The 3×3×6 cycle is ahead of the 4×4 plans by 1–3 points at every depth: slightly more
saving, slightly less traffic, and larger leaves (n/54 against n/64 after three levels).
The model assumes the rectangular leaf GEMMs run at the square GEMM's rate.  Measured
(Accelerate through numpy's f32 matmul, best of ten interleaved calls, outputs
preallocated, equal flops): square 2165³ 3353 GFLOP/s; the ⟨3×3×6⟩ leaf (2730, 2730, 1365)
3262, the ⟨3×6×3⟩ leaf (2730, 1365, 2730) 3521, the ⟨6×3×3⟩ leaf (1365, 2730, 2730) 3169;
the 4×4 leaf 2047³ 3373.  After two levels the cycle's leaves (910, 455, 455) run at 2839
against 2512 for the 4×4 plan's 511³.  Within 5% either way at one level and 13% ahead at
two, so the assumption holds.

## Orbit minima (`orbit_rect.py`, GL₃ × GL₃ × GL₆, 8 starts)

| class, point | amp (ratio to classical) | γ∞,2 (ratio) | γ₂ |
|---|---|---|---|
| ⟨3×3×6:40⟩ DPS-accurate point | 2.046 (2.363) | 20.0 (6.67) | 104.09 |
| ⟨3×3×6:40⟩ orbit minima | 1.942 (2.242) | 19.1 (6.37) | 104.09, DPS's point |
| ⟨3×6×3:40⟩ DPS-accurate point | 3.122 (2.550) | 33.0 (5.50) | 104.09 |
| ⟨3×6×3:40⟩ orbit minima | 2.746 (2.242) | 23.4 (3.90) | 104.09, DPS's point |
| ⟨4×4×4:48⟩ accurate_262, control | 2.828 (2.828), its orbit's amp minimum | 22.63 (5.66) | 154.51 |

DPS's 3×3×6 point sits 5% above its class's amp floor and 5% above its γ∞,2 floor; their
3×6×3 point 14% and 41% above (that orientation's γ∞,2 floor, ratio 3.90, is far below
the 4×4's 5.66).  The ±1 Smirnov point of the same class (`3x3x6_40`, amp ratio 10.8)
reaches the same floors, so the class carries them, not the point.  In amplification per
4×4-equivalent saving the floor is 2.17 against accurate_262's 2.83; DPS's exact points
give 2.28 and 2.45.  A better exact point for the 3×6×3 orientation (amp 2.746 at the
floor) is worth a search with the dyadic tools of `../gamma3` and `../gamma5`.  With eight
starts the control did not leave accurate_262 for the 4×4 orbit's γ∞,2 point at 21.41 that
`../gamma5/orbit5.py` reaches from DPS's `accurate` point, so these floors may be slightly
high.

## What it would take

The library executes square levels on square blocks (one block size per level); the
3×3×6 family needs rectangular blocks (A blocks M/g1 × K/g2, B blocks K/g2 × N/g3, C blocks
M/g1 × N/g3), a planner over (M, K, N) sub-problems instead of n, three level types, and
kernels generated from DPS's three programs (`gen_kernels.py` is already shape-agnostic).
That is the "rectangular shapes" item of plan item 7, a few days of work on the C library
(the Rust port after), after which the three orientations are measured against the D48
plans exactly as the 5×5 level was.  Sizes: one level needs n divisible by 6, the cycle by
54; the library pads.

## Files

- `levels.py OUT.csv`: the per-level metrics of every scheme on disk (AlphaEvolve's 15
  shapes from the Hell's Bells copy of their file, Apache 2.0; Kauers–Wood's and Kemper's
  29 rectangular schemes; PLinOpt's small and rectangular ones including DPS's accurate
  variants; Kronecker composites); `levels.csv`.
- `cost_rect.py [n]`: the plan cost model with rectangular levels.
- `orbit_rect.py OUT.csv PREFIX g1 g2 g3`: orbit minima under rectangular isotropies;
  `orbit_*.csv`, `orbit_rect.log`.
