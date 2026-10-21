# cand48 — rank-48 4×4 orbit candidates over Z[½]

`sparse68`: a representative of the rank-48 class found by `../orbit48.py`
(GL(4, Z[½])³ annealing on the operation floor with a sparsity penalty,
λ = 0.3) from PLinOpt's `4x4x4_48_202` (Patel) point.  Floor 159 =
42/45/40 + 32, 68 non-unit coefficients (±½, ±2), all 4096 Brent
equations verified over Q (orbit48) and by PLinOpt's MMchecker.

Programs `sparse68_{L,R,P}.slp` are PLinOpt-optimizer outputs refined to
a pair-level fixed point by `../prune_loop.py` (L 70, R 67, P 101 = 238),
with L further reduced to 67 by the exact window LNS below: **235
operations** = 67 + 67 + 101 (SLPchecker-counted, additions + scalings).  For
comparison the same pipeline on Patel's own representative converges at
68 + 74 + 111 = 253 (final), while his stored programs total 202 (54+2, 54+2, 90),
so the published counts come from a further "heavy" refinement stage that
the base optimizer, random restarts, triples, chartreuse and long random
walks do not reproduce (2026-10-21 calibration).  Not a record: 238 > 202.

Step 3 (exact window LNS, `../qexact.py` + `../exactlns.py`, 2026-10-21):
three improvements on L (70 -> 67 = 65 adds + 2 scalings, 16-line windows
with up to four helpers; log `sparse68_L_exactlns.log`; total 235) and
none on R, P or on any side of Patel's point; the other consecutive windows of up to 16 lines
are provably optimal with at most two helpers each, so most of the slack
is in the choice of computed signals, not in how a window computes them.
The heavy stage is now known: Patel's own search code is public
(github.com/rp440/matmul-4x4-48-202, `search/`, CC0) -- a value-set LNS
(propose new signal vectors, reverse-delete while the set stays closed
under one-gate productions, accept equal-cost and best+1 moves, z3 sign
planning) that takes his point from PLinOpt's programs to 56 + 56 + 90.
Next: apply that search to `sparse68`.
