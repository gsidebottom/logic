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

## 3x3, same protocol

| scheme                  | multiplies | total ops | ONLINE ops |
|-------------------------|-----------:|----------:|-----------:|
| naive-27                |         27 |        18 |     **18** |
| rank-23 (online-40 winner, signed) | 23 | 64 (PLinOpt) | **44** PLinOpt / **40** our exact |

Both gated exact (compute 3x3 matmul on random integer matrices); the
rank-23 signed coefficients were extracted from the winner's bits via
the sign-model machinery, which independently validates that pipeline
(the lifted scheme really multiplies matrices).

Note: our exact method (exact signed side minimization + transposition-
principle exact C) returns 40 where PLinOpt at 24 reps returns 44 — our
tooling beats the general-purpose optimizer by 4 ops on this instance.

Crossover: rank-23 saves 4 multiplies and costs 22 extra online adds
(40 vs 18), so it wins iff c_mul/c_add > 5.5 — the same shape as 4x4's
6.5 crossover between Strassen^2-49 and naive-64. Both dimensions tell
one story: rank reduction is an online LOSS unless multiplies are
>5-7x the cost of additions, which is true for constraint counting
(private weights) and false for witness generation.

## The 4x4 sweep is blocked: found4r schemes do not lift to Z

Floors over all 40,238 rank-49 mod-2 schemes: 35 seconds, global min
116 (4 schemes), Strassen^2-49 mid-pack at 123.  So the DB *looked*
like it held ~5% better online candidates.

Then sign-lifting (lift4.py: support fixed, each coefficient +-1, a
Brent equation with k covering terms and RHS r needs exactly (k-r)/2
terms negative, term sign = XOR of its three coefficient signs; SAT,
then exact evaluation against 4x4 matmul):

  floor 116 (all 4):        0 lifted
  floor 117 (40 sampled):   0 lifted
  floors 118-123 (30 each): 0 lifted
  TOTAL: 0 / 224

Lifter validated on Strassen^2-49's own support (LIFTED + VERIFIED),
and the candidates are genuine mod-2 solutions (brent.py verifier: 0
violations).  For contrast, in 3x3 every one of the 145,951 scored
schemes had a sign model — lifting is essentially free there.

Conclusion: found4r is a GF(2)-only population.  Its members satisfy
the Brent equations mod 2 but are not matrix-multiplication algorithms
over Z, so their floors are not attainable and the DB cannot supply a
better rank-49 scheme.  Strassen^2-49 (online 145) stands as the only
verified rank-49 scheme we hold.

To revive the 4x4 hunt one must search where liftability is
guaranteed: gauge/orbit images of verified schemes (the route the
DPS-48 artifact used), a direct search over Z (flip48p's field
engine), or lifts with larger coefficient alphabets.
