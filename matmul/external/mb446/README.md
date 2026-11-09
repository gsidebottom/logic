# Two <4,4,6> schemes reduced mod 2

- `446-74-mod0.m` (sha256 e521a5684a4c9e4e0ec0532c8ec294262f9bc1f7d8e7ca051773eac0fc9e796d): Jakob Moosbauer's flip-graph <4,4,6>:74 over Z, from the Perminov catalog copy
  `schemes/known/jakobmoosbauer_flips/446-74-mod0.m`.  F2 image `mb446_74_mod2.bits`: rank 74 (nothing vanishes
  mod 2), 0 of 9216 Brent equations violated.
- `meta446_73_k16a37de3456570e8.m` (sha256 a179fcdbfcb239d6f54280c9070725a6b4bf57a2fae966c28653412a8b9a7d18): the catalog's `schemes/known/meta_flip_graph/446/k16a37de3456570e8.m`,
  a <4,4,6>:73 with rational coefficients (thirds).  An odd denominator is a unit mod 2, so the scheme reduces:
  `meta446_73_mod2.bits`, rank 73, 0 of 9216 Brent equations violated.

Both converted with `/usr/bin/python3 -I matmul/m_to_bits.py in.m 4 4 6 out.bits` on 2026-11-09 (Mathematica list
format: {A (4x4), B (4x6), C^T (6x4)} per product; the converter tries both C readings and checks Brent).  Use:
projection parents two column-kills from <4,4,4> for the Tomar-line seed pools, `matmul/tomar_line/proj/make_mb2_pools.sh`.
