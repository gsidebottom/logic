# Moosbauer's <4,5,5>:76 over Z, reduced mod 2

Source: the Perminov catalog copy of Jakob Moosbauer's flip-graph repository,
`schemes/known/jakobmoosbauer_flips/455-76-mod0.exp` (sha256 1ba4f15d64f5385580ca15fd40c849950c6d831e44528e203c80d92079d627e8), 76 products with
integer coefficients.  `mb455_76_mod2.bits` is its image over F2 (no product vanishes mod 2, rank 76,
0 of 10000 Brent equations violated; c read as c_(j,i)), produced by
`/usr/bin/python3 -I matmul/exp_to_bits.py 455-76-mod0.exp 4 5 5 mb455_76_mod2.bits` on 2026-11-09.

Use: a projection parent two steps from <4,4,4> (one inner direction and one column to kill) for the Tomar-line
seed pools, `matmul/tomar_line/proj/make_mb2_pools.sh`.
