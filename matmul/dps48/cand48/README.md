# cand48 — rank-48 4×4 orbit candidates over Z[½]

`sparse68`: a representative of the rank-48 class found by `../orbit48.py`
(GL(4, Z[½])³ annealing on the operation floor with a sparsity penalty,
λ = 0.3) from PLinOpt's `4x4x4_48_202` (Patel) point.  Floor 159 =
42/45/40 + 32, 68 non-unit coefficients (±½, ±2), all 4096 Brent
equations verified over Q (orbit48) and by PLinOpt's MMchecker.

Programs `sparse68_{L,R,P}.slp` are PLinOpt-optimizer outputs refined to
a pair-level fixed point by `../prune_loop.py`: L 70, R 67, P 101 =
**238 operations** (SLPchecker-counted, additions + scalings).  For
comparison the same pipeline on Patel's own representative converges at
68 + 74 + 111 = 253 (final), while his stored programs total 202 (54+2, 54+2, 90),
so the published counts come from a further "heavy" refinement stage that
the base optimizer, random restarts, triples, chartreuse and long random
walks do not reproduce (2026-10-21 calibration).  Not a record: 238 > 202.
