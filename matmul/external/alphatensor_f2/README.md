# AlphaTensor's F2 factorizations as .bits seeds

The twenty mod-2 factorizations published with AlphaTensor (Fawzi et al.,
Nature 2022; `algorithms/factorizations_f2.npz` in github.com/deepmind/alphatensor,
Apache 2.0), converted to this repository's .bits layout (all a factors, then
all b, then all c; brent.py-compatible) by `at_all.py` (safe unpickler, every
factorization checked against the matmul tensor before writing).  File
`at{n1}{n2}{n3}_{rank}.bits`; the ranks are AlphaTensor's: 2x2x2 7, 2x2x3 11,
2x2x4 14, 2x2x5 18, 2x3x3 15, 2x3x4 20, 2x3x5 25, 2x4x4 26, 2x4x5 33, 2x5x5 40,
3x3x3 23, 3x3x4 29, 3x3x5 36, 3x4x4 38, 3x4x5 47, 3x5x5 58, 4x4x4 47, 4x4x5 63,
4x5x5 76, 5x5x5 96.  `at_to_bits.py` converts one named factorization.
Used by matmul/tomar_line (projected seed pools, capacity checks).
