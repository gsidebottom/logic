# logic

Research monorepo for SAT-adjacent search and verification experiments.
Its headline result:

## 3×3 matrix multiplication in 23 multiplications and 55 additions

**The lowest addition count ever published for a rank-23 (23-multiplication)
exact 3×3 matrix-multiplication scheme** — one below the previous record
of 56 (Y. Sun, arXiv:2604.27645, Apr 2026) — in the standard model:
binary ± additions, negation free, no change of basis, coefficients
±1, valid over any ring (the algorithm is fully non-commutative and
recurses on block matrices).

And it is final for every known class: **no 54-addition scheme exists
anywhere in the published catalogue** — across all 17,376 de Groote
classes of the Heule–Kauers–Seidl database, every representative,
every sign model (plus the 53 novel classes found in this repo). A
sub-55 scheme would require a rank-23 class nobody has catalogued.

| artifact | where | check it |
|---|---|---|
| The 55-operation program | [matmul/external/i19-55adds-slp.txt](matmul/external/i19-55adds-slp.txt) | `python3 matmul/verify_slp_file.py matmul/external/i19-55adds-slp.txt --trials 5000` |
| Runnable Rust version + fuzz vs naive | [src/mm55.rs](src/mm55.rs) | `cargo test --release --lib mm55::` |
| Machine-checked proof (Lean 4 + Mathlib) | [matmul/mm55proof/](matmul/mm55proof) | `cd matmul/mm55proof && lake exe cache get && lake build` |
| Paper (method + reproduction) | [doc/matmul_adds_paper.pdf](doc/matmul_adds_paper.pdf) | §7 lists every command |
| Archived artifacts (citable) | [DOI 10.5281/zenodo.21240904](https://doi.org/10.5281/zenodo.21240904) | program + verifier + proof + snapshot |

The method: both halves of a scheme's additive cost are minimized
**exactly** — the input sides as addition-chain covering
([matmul/sidemin.py](matmul/sidemin.py)), and the output side via the
**transposition principle** (Tellegen; [matmul/tcmin.py](matmul/tcmin.py)),
which reduces it to the same tractable chain-covering problem plus a
constant. Greedy common-subexpression elimination — the engine behind
the whole 60 → 56 record chain — is an upper bound only; the exact
output side is where the extra addition was found. The no-54 theorem
replays the same argument over GF(2), where it lower-bounds every
sign model at once ([matmul/gf2min.py](matmul/gf2min.py),
[matmul/cfloor.py](matmul/cfloor.py)).

The Lean proof certifies, over a general non-commutative ring, that
the 55-operation program computes the matrix product — sorry-free,
`#print axioms` audited, in Mathlib's own `Matrix` API.

## Also in this repo

- **53 new rank-23 3×3 schemes** inequivalent to the entire published
  database ([doc/matmul_53_3x3_schemes.pdf](doc/matmul_53_3x3_schemes.pdf)),
  found by native-ANF stochastic local search on the Brent equations.
- **SAT benchmarks** with known ground truth from the additive-
  complexity work ([doc/matmul_cxlb_satcomp.pdf](doc/matmul_cxlb_satcomp.pdf)).
- A native-ANF SLS solver for the Heule matrix-multiplication
  challenges (`src/bin/anf.rs`), GF(2) orbit scanners (`src/floors.rs`),
  flip-graph engines, and other search tooling — see `doc/` and the
  git history.

## License

Apache-2.0 (see [LICENSE](LICENSE)).
