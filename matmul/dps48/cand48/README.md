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

**Patel's LNS applied to sparse68 (2026-10-21, `../patel/`): 205 = 56 + 58 +
91**, stored as `sparse68_205_{L,R,P}.slp` (SLPchecker syntax; counts are
PLinOpt's additions + scalings).  L and R: his `rebuild3.py`, 4 workers x
30 min each, every worker converging to the same cost (L 59, R 61 in his
model, which also charges the 4 + 4 output negations that PLinOpt counts
as free).  P: his direct search never left 101, so P was optimized through
its transpose (a 48x16 map like L and R; `../patel/patel_phase.py` drives
his `Search` class on one map): P^T 63 -> P = 59 + 32 = 91 by the
transposition principle (PLinOpt's `transpozer`).  Verified three ways:
SLPchecker against the sms matrices, MMchecker on the matrices, and
`../slp48check.py` (exact Brent over Q; also counts Patel's model: 213).
Three operations above Patel's 202.  Running next: the same pipeline over
the 90 annealer pool points (`../patel/sweep.py`, successive halving).

**Rust port, 2026-10-21 10:00: 204 = 56 + 58 + 90** (`sparse68_204_{L,R,P}.slp`;
`sparse68_204_Pt.slp` is the 58-operation P^T program).  `src/bin/lns48.rs`
reimplements the value-set LNS with PLinOpt's objective at ~80 iterations/s
per thread (20x the z3-free Python, 70x the original); on P^T it found 58
where the Python runs had stalled at 59 (P = 58 + 32 = 90).  Verified by
SLPchecker on each side, by the exact Brent check (`../slp48check.py`), and
the P^T program's transposition by PLinOpt's `transpozer`.

**10:10: 203 = 55 + 58 + 90** (`sparse68_203_{L,R,P}.slp`).  `lns48` seeded
from the MATRIX ALONE (`--sms`, a naive chain program of 163 values that the
reverse deletion prunes to 85 before the search starts) reached L = 55 in 20
seconds -- below the 56 that every run seeded with PLinOpt's optimizer output
(Python and Rust, 4 x 30 min) had converged to: the seed decides the basin,
and cheap restarts from different seeds now matter more than long runs.
Verified by SLPchecker (53 + 2) and the exact Brent check.  One above the
202 record.

`sparse68_203n_{L,R,P}.{slp,sms}`: the same 203 triple after `../signnorm48.py`
(sign-aware re-emission; L and R output negations absorbed into the signs of
P's inputs, so rows of L and R and columns of P may be negated together --
the sms files are the normalized matrices): **zero negations, 203 in Patel's
model as well as PLinOpt's**.  SLPchecker on its own matrices (53+2, 56+2,
90+0), MMchecker (rational mode) and the exact Brent check all pass.

**10:07: 202 = 55 + 58 + 89 -- a tie with Patel's record** (`sparse68_202_*`,
normalized `sparse68_202n_*`: zero negations, 202 in both cost models).
`../patel/restarts.sh` (12 naive seeds x 180 s per side, lns48): L 55 on all
12 seeds, R 58 on all 12, P^T 57 on one seed (`sparse68_202_Pt.slp`; the
others 58-59) -> P = 89.  Verified: SLPchecker on each side (53+2, 56+2,
89+0; the normalized triple against its own sms), MMchecker x5 (rational
mode) and the exact Brent check.

## 2026-10-21 10:30 -- **201 = 55 + 57 + 89: a new record (Patel's 202)**

`p005_201_{L,R,P}.{sms,slp}` (+ `p005_201_Pt.slp`, the 57-operation P^T
program) and the sign-normalized `p005_201n_{L,R,P}.{slp,sms}`; a second
point, `p010_201_*`, reaches the same 201.  Both points come from the
orbit48 annealer's lambda = 0.3 pool (pool_l0.3 cand005 / cand010: floor 156
= 42/44/38 + 32, 72 non-unit coefficients), found by `../patel/sweep.py`
with the Rust engine (`src/bin/lns48.rs`, matrix-only seeds): stage A (30 s
per side) 202, stage B (120 s per side) 201 = L 55 + R 57 + P (P^T 57 + 32).

Verification of the normalized triple (zero negations, so the count is 201
in Patel's model as well as PLinOpt's): SLPchecker against its own matrices
(53+2, 55+2, 89+0); MMchecker x5 default and x3 at 40-bit values; the exact
Brent check (`../slp48check.py`, 0/4096 failures); Patel's own `slp.py`
checker ("Total linear ops: 201", 4096 tensor identities, typed DAG
verified).  The raw triple verifies the same way against the point's
original matrices (count 201 in PLinOpt's model; 227 in Patel's, the
difference being free output negations).

**Contributed to PLinOpt (2026-10-21 13:10)**: https://github.com/jgdumas/plinopt/pull/23
(`data/4x4x4_48_201_{L,R,P}.{sms,slp}` = the normalized `p005_201n` triple with
PLinOpt-style title comments; the PR cites the Lean proof
`proof/Mm/Ring_4x4_48_201.lean`).

**14:20: a third 201 structure, `lam01c0_201_*`**: the annealer at lambda = 0.1
(non-unit coefficients cheap) reaches floor-150 points with side floors
40/40/38 and 104 non-unit coefficients (Patel's kind of point, balanced);
`pool3/lam01_p005/cand000` gives **201 = L 56 + R 56 + P 89** (restarts.sh, 6
seeds x 300 s: L 56 x6, R 56 x5, P^T 57 x2).  With the 55/57/89 family
(p005, p010, ...) and its L/R mirror, every proxy-optimal structure tried
lands on exactly 201.
