# Zenodo deposit kit — v1.0-mm55

Everything to paste into the Zenodo upload form (or into a new version
of an existing record). The deposit gives the artifacts a citable DOI,
referenced from the arXiv paper.

## Files to upload

- `matmul/external/i19-55adds-slp.txt` — the 55-operation program
- `matmul/external/i19-perminov56.bits` — the committed representative
- `matmul/verify_slp_file.py` — independent from-scratch verifier
- `src/mm55.rs` — runnable Rust transcription + fuzz tests
- `matmul/mm55proof/` (now `proof/` in the repo; zip of the Lake project, without `.lake/`) — Lean proof
- `doc/matmul_adds_paper.pdf` — the paper
- (optional) a full `git archive v1.0-mm55` tarball of the repository

## Metadata

**Title:** A 55-Addition Rank-23 Scheme for 3×3 Matrix Multiplication
— artifacts, verifier, and machine-checked proof

**Authors:** Sidebottom, Greg

**Description:**
Artifacts for the first 55-addition, 23-multiplication exact 3×3
matrix-multiplication scheme (previous record: 56 additions; Y. Sun,
arXiv:2604.27645). The scheme uses ±1 coefficients, binary ± additions
with free negation, no change of basis, and is valid over any ring
(fully non-commutative; recurses on block matrices). Included: the
explicit 55-operation straight-line program; an independent verifier
(exact integer and non-commutative block trials, operation count); a
runnable Rust transcription with fuzz tests against the naive
27-multiplication algorithm; a sorry-free Lean 4 + Mathlib proof that
the program computes the matrix product over a general non-commutative
ring; and the paper, which also proves that no 54-addition scheme
exists anywhere in the published Heule–Kauers–Seidl catalogue (17,376
de Groote classes, every representative, every sign model).
Developed in an extended interactive collaboration with Claude
(Anthropic); every claim is mechanically checkable by the included
tools.

**Keywords:** matrix multiplication; bilinear complexity; additive
complexity; Strassen-like algorithms; straight-line programs;
transposition principle; Tellegen; Lean; formal verification; SAT

**License:** Apache-2.0

**Related identifiers:**
- `https://github.com/gsidebottom/logic/tree/v1.0-mm55` (isSupplementTo)
- arXiv DOI once assigned (isDescribedBy)

**Version:** v1.0-mm55
