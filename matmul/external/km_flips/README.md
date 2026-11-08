# Kauers-Moosbauer flip-graph schemes as .bits seeds

`445-60-mod2.exp`: the <4,4,5> scheme of rank 60 over F2 published with
M. Kauers, J. Moosbauer, *Flip graphs for matrix multiplication*, Proc. ISSAC 2023,
381-388, doi:10.1145/3597066.3597120 (arXiv:2212.01175), the one scheme per format the
paper releases, from github.com/jakobmoosbauer/flips (solutions/445-60-mod2.exp, GPL-3.0,
fetched 2026-11-07; sha256 3b134ae7c85225084185dc02d98c3889b11038b796bd37b85f7913472b0e15b7).
The record for the format over F2 (AlphaTensor's is 63; over any field the paper's 62 and
AlphaEvolve's 61 since 2025).

`km445_60.bits`: the same scheme in this repository's .bits layout (all a factors, then
all b, then all c, row-major; project_f2.py's load_bits), converted by ../../exp_to_bits.py,
which reads the .exp trilinear form sum a_ik b_kj c_ji (so c is indexed (j,i)), tries both
readings of c and writes the one that satisfies all 6400 Brent equations (the transposed
reading; the direct one is out of range).  Independently re-checked with project_f2.check.

Use: projected seed pools for the 4x4 descent (matmul/tomar_line section 3): one column
projection of a rank-60 <4,4,5> scheme is a 4x4 scheme of rank 56, three ranks below the
pools from AlphaTensor's 63.
