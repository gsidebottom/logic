# AlphaEvolve's <4,4,5>:61, reduced mod 2 (2026-11-08)

Source: Perminov's collection github.com/dronperminov/FastMatrixMultiplication, file
schemes/known/alpha_evolve/4x4x5_m61_mod0.json (local clone matmul/perminov_cache/repo at commit
3ee3284 of 2026-10-28; sha256 of the file 2564f615c0dbfb7094d77f41c9b79d89206efc8affeeddd83f85b29aa15035a1).  The scheme is over Z
(z2: false); all 61 products survive reduction mod 2, so the F2 scheme has rank 61 as well.

ae445_61.bits: the repository's layout (the 61 alpha blocks (4x4), then the betas (4x5), then the gammas
(4x5), row-major, one line), written by matmul/json_to_bits.py after checking all 6400 Brent equations over
F2; the JSON's w vectors index C transposed (c_(j,i)), as Kauers-Moosbauer's .exp files do.

Use: the third parent of the projected 4x4 seed pools (tomar_line/proj/make_ae_pools.sh): one projection
drops 4, so the seeds sit at 57, between the 56 of Kauers-Moosbauer's <4,4,5>:60 and the 59 of
AlphaTensor's <4,4,5>:63.
