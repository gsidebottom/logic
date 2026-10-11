# Zenodo deposit kit — v1.0-ks51

Everything to paste into the Zenodo upload form. Files are staged in
`zenodo-upload-ks51/` (gitignored); the tag `v1.0-ks51` marks the
repository state (push it: `git push origin v1.0-ks51`).

Depositing now timestamps the 51 result publicly with a citable DOI;
the paper PDF is a draft (sweep table incomplete) and can be revised
through Zenodo's versioning, as can the final arXiv text.

## Files to upload

- `matmul_3x3_rank23_add51.pdf` — the paper (draft of 2026-10-11)
- `Ring51.lean` — the machine-checked scheme + theorems (standalone copy)
- `proof-lake-project.zip` — the full Lean/Lake project (without
  `.lake`; reproduce with `lake exe cache get && lake build Mm.Ring51`)
- `ks51-certificates.tar.gz` — `matmul/external/ks51/`: the F2 leg
  certificates, the signed legs of sign model 21, the model-loop log
  with the three signed chains, and the class bits
- `ks51-tools.tar.gz` — the exact searchers (`fbmin.rs`, `fbsmin.rs`),
  drivers (`fbsweep.py`, `fbsloop.py`), lifting/gauge/model/SMT tools,
  and the Lean generator `gen_ring51_lean.py` (word-ring gate included)
- `logic-v1.0-ks51.tar.gz` — full `git archive` of the repository at
  the tag (93 MB)

## Metadata

**Title:** A 51-Addition-per-Step Rank-23 Scheme for 3×3 Matrix
Multiplication in the Karstadt–Schwartz Model — artifacts, exact
searcher, and machine-checked proof

**Authors:** Sidebottom, Greg Allan

**Upload type:** Software (or Dataset; Software matches the mm55 record)

**License:** Apache-2.0

**Version:** v1.0-ks51

**Publication date:** 2026-10-11

**Keywords:** matrix multiplication; bilinear complexity; additive
complexity; alternative basis; Karstadt–Schwartz; Strassen-like
algorithms; Lean; formal verification; exact search

**Description:**

Artifacts for a rank-23 bilinear scheme for 3×3 matrix multiplication
using 51 additions per recursive step in the alternative-basis
(Karstadt–Schwartz) cost model — one addition below the previous best
of 52 (Nielsen, arXiv:2609.06588). The scheme is valid over every
ring (products keep factor order; it recurses on block matrices) and
its correctness is machine-checked in Lean 4 / Mathlib:
`Ring51.correct` depends on the axiom `propext` alone, and the
Matrix-API theorem `rank23_add51_scheme_eq_mul` (the scheme equals
Mathlib's `A * B`) on Lean's three standard axioms. The count is
exactly optimal for the scheme's equivalence class (HKS class
i12w211c23fg): the deposit includes the exact free-basis minimization
tools whose negative answers are finite exhaustions, the F2 and signed
leg certificates, the integer sign model, and the generator whose
word-ring verification over Z<A,B> re-checks the emitted program.
The same tools prove the previous record of 52 exactly optimal for its
own class. Found by exact exhaustive search over the
Heule–Kauers–Seidl database of rank-23 schemes.

Reproduction: unpack `proof-lake-project.zip`, then
`lake exe cache get` once, then
`find .lake/build -name "Ring51.*" -delete && lake build Mm.Ring51`
(expected: `Built Mm.Ring51` in ~6–8 s with the axiom audits above).

**Related identifiers:**

- `https://github.com/gsidebottom/logic` (is supplemented by this upload)
- `10.5281/zenodo.21240904` (continues: the 55-addition flat-model record)
- `arXiv:2609.06588` (is new version of / references — use "references")

## Checklist

1. `git push origin v1.0-ks51` (and master if not current).
2. zenodo.org → New upload → add the six files from `zenodo-upload-ks51/`.
3. Paste metadata above; Publish. Record the DOI.
4. Put the DOI into `doc/matmul_3x3_rank23_add51.tex` (Artifacts
   paragraph) and rebuild; it rides into the arXiv version.
5. When the sweep finishes and the paper freezes: Zenodo "New version"
   with the final PDF and the sweep results CSV.
