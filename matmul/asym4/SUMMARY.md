# 4x4 rank 48 vs 49 vs 64 under the asymmetric (free-weight-side) objective

Question: for zkML inference (weight matrix fixed, its linear
combinations precomputed once), does a HIGHER-rank scheme with more
add-asymmetry beat the rank-48 record?

Protocol: PLinOpt (Dumas-Grenet-Pernet-Sedoglavic), the same optimizer
and same budget (24 repeats x direct+transposed-kernel modes) for every
scheme; online cost = (non-free side) + P, minimized over the 6 tensor
orientations. Control: our DPS-48 measurement reproduces the README's
independent number at equal budget (365 here vs 364 there).

| scheme        | multiplies | total ops | ONLINE ops (weight side free) |
|---------------|-----------:|----------:|------------------------------:|
| naive-64      |         64 |        48 |                        **48** |
| Strassen^2-49 |         49 |       208 |                       **145** |
| DPS rank-48   |         48 |       365 |                       **248** |

Schemes gated exact before measurement: Strassen^2 and naive both
verified to compute 4x4 matmul on random integer matrices (mk49.py).

## Findings

1. YES — higher rank wins decisively on this objective. Rank-49 beats
   the rank-48 record by **103 online ops** (145 vs 248) at a cost of
   one extra multiply. Rank-49 dominates rank-48 for any cost ratio
   c_mul/c_add < 103, i.e. essentially always.
   The rank record is the WORST of the three online: its rational
   coefficients buy the 48th product with scalar multiplications and
   many extra additions.

2. BUT the same logic runs all the way down to naive. The extreme of
   add-asymmetry IS the naive scheme: its side matrices are single
   entries, so it needs ZERO side additions (measured L=R=0), and only
   48 output adds. Naive beats Strassen^2-49 whenever
   15*c_mul < 97*c_add, i.e. c_mul/c_add < 6.5.

3. Three regimes, and the orderings are exactly reversed:
   - Constraint count (R1CS/AIR, PRIVATE weights): adds are free,
     multiplies cost -> rank-48 wins (48 < 49 < 64).
   - Witness generation (BabyBear silicon, mul ~ 2-3x add):
     c_mul/c_add ~ 3 < 6.5 -> naive-64 wins.
   - Middle band 6.5 < c_mul/c_add < 103: Strassen^2-49 uniquely wins.
   Public-weight layers are constant linear maps and cost zero
   multiplication constraints; rank optimization is irrelevant there
   (see doc/matmul_zkml_paper.md:119).

The substrate law again: multiplies, additions, or bytes decide the
winner depending on the machine — here the SAME question has three
different right answers.
