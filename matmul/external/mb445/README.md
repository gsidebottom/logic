# Moosbauer's <4,4,5> scheme of rank 62 over Z, reduced mod 2, as a .bits seed

`445-62-mod0.exp`: the integer <4,4,5> scheme of rank 62 from the flip-graph paper's data
(M. Kauers, J. Moosbauer, *Flip graphs for matrix multiplication*, ISSAC 2023; github.com/jakobmoosbauer/flips,
GPL-3.0), taken 2026-11-09 from Perminov's catalogue clone
(matmul/perminov_cache/repo/schemes/known/jakobmoosbauer_flips/445-62-mod0.exp; sha256 6d548486de3b3f7ee250eab7132c765da0358a1ff614010fd8446b19d816add8).
Coefficients up to 8 in absolute value.

`mb445_62_mod2.bits`: its image over F2 in this repository's .bits layout (all a factors, then all b, then
all c, row-major), by ../../exp_to_bits.py (generalised 2026-11-09 to signed integer coefficients and bare
monomial factors; coefficients reduced mod 2, products with a factor vanishing mod 2 dropped).  No product
vanishes: rank 62 over F2, all 6400 Brent equations verified (c read as c_(j,i), as in the KM file).
A different scheme from the rank-60 F2 parent in ../km_flips (which gave the fifth rank-47 class, 2026-11-07).

Use: projected 4x4 seed pools for the descent (matmul/tomar_line section 3; make_mb_pools.sh), the third
<4,4,5> parent after Kauers-Moosbauer 60 (positive) and AlphaEvolve 61 (negative).
