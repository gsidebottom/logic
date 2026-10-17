# Zenodo new-version kit — KS-51 deposit, v2.0

**PUBLISHED 2026-10-17:** https://zenodo.org/records/23441986,
doi:10.5281/zenodo.23441986 (concept doi:10.5281/zenodo.23305910 now
resolves to it). Eight files, all MD5-matched to the staging from tag
`v2.0-ks51` (da2b9c0); description, Notes (changes since v1) and both
related works as below.

Existing record: **doi:10.5281/zenodo.23305912** (v1.0-ks51, 2026-10-11).
Publish this as a **New version** of that record (zenodo.org → the
record → "New version"), so the concept DOI keeps resolving to the
latest version and v1 stays citable.

Stage the files from the deposit tag (every file comes from `git
archive` / `git show` at the tag, never the working tree):

```
git tag v2.0-ks51
python3 matmul/zenodo_stage.py ks51 v2.0-ks51 v2.0
```

This writes `zenodo-upload-ks51-v2.0/` (gitignored).

## Files to upload (replace all v1 files)

- `matmul_3x3_rank23_add51.pdf` — the paper (v2)
- `Ring51.lean` — our 51-addition scheme, machine-checked (standalone)
- `SP51.lean` — Stapleton–Perminov's scheme, machine-checked (new)
- `SP51Optimal.lean` — their 51 kernel is optimal for its class,
  machine-checked (new; kernel `decide`, ~4 minutes)
- `proof-lake-project.zip` — the full Lean/Lake project (no `.lake`;
  reproduce with `lake exe cache get && lake build Mm.Ring51 Mm.SP51
  Mm.SP51Optimal`)
- `ks51-certificates.tar.gz` — `matmul/external/ks51/` (leg
  certificates, sign models, final sweep CSVs, the three novel
  52-class representatives), `matmul/external/sp51/` (S-P's published
  program and certificate), `matmul/external/flat55/` (the 616-class
  flat-floor results)
- `ks51-tools.tar.gz` — exact searchers and drivers (fbmin, fbsmin,
  floors with `--exact-total`, the cyclic enumerator, the flip walker,
  sweep/model/Lean-generator scripts)
- `logic-ks51-v2.0.tar.gz` — full repository snapshot at the tag

## Metadata changes

**Version:** v2.0-ks51

**Publication date:** 2026-10-17 (or the day you publish)

**Title (unchanged):** A 51-Addition-per-Step Rank-23 Scheme for 3×3
Matrix Multiplication in the Karstadt–Schwartz Model — artifacts,
exact searcher, and machine-checked proof

**Description:** replace the first paragraph with:

Artifacts for rank-23 bilinear schemes for 3×3 matrix multiplication
using 51 additions per recursive step in the alternative-basis
(Karstadt–Schwartz) cost model. The count 51 was first posted by
Stapleton and Perminov (arXiv:2609.32388, 2026-09-26); this work is
independent and complementary — exactness and breadth. A complete
exact sweep of the Heule–Kauers–Seidl database finds exactly four
51-classes, all in one invariant family, and no 50 at any floor. Our
scheme (class i12w211c23fg) and Stapleton–Perminov's are both
machine-checked in Lean 4 / Mathlib over arbitrary rings, and a further
kernel-checked Lean proof (SP51Optimal.lean) shows that
Stapleton–Perminov's 51 is optimal for its class. Exact orbit-wide F2
flat floors prove their one-shot cost of 56 optimal for their class, and
show that the flat-55 record is unique to its class across the
database.

(Keep the remaining v1 paragraphs on reproduction and verification;
update the reproduction command to `lake build Mm.Ring51 Mm.SP51
Mm.SP51Optimal`.)

**Related identifiers (add):**

- `arXiv:2609.32388` — references (Stapleton–Perminov's 51)
- `10.5281/zenodo.21240904` — continues (the 55-addition flat record;
  its v1.1 carries the database-wide uniqueness of 55)

## Changes since v1.0-ks51 (for the version notes)

- **Priority corrected:** v1's abstract said 51 improved the previous
  best of 52 without acknowledging Stapleton and Perminov's 51
  (arXiv:2609.32388, 2026-09-26). v2 credits it and positions this
  work as independent and complementary.
- **Four 51-classes, not two:** the sweep, completed variant-aware,
  adds Stapleton–Perminov's class (i12w219c23ci-008, which is
  Perminov's earlier cn119 class) and a fourth (i12w227c23ci-012,
  ring-valid). All four lie in HKS family i12. No 50 exists in the
  database at any floor.
- **Stapleton–Perminov's scheme Lean-verified** (`SP51.lean`), and
  its kernel's class-optimality machine-checked (`SP51Optimal.lean`:
  from any nine starting vectors and after any invertible change of
  coordinates, its legs need at least 13, 12 and 12 additions; proof by
  counting sum triples, finite facts by kernel `decide`).
- **Basis-change (conversion) costs, stated precisely:** per
  representative and sign model; Stapleton–Perminov's 5 is minimal
  over all 128 signings of their representative, and their one-shot
  56 is optimal for the whole class (exact F2 flat floor 56). Our
  class's flat floor is 57.
- **Flat-55 record unique to its class** across the database (exact
  check of the 616-class output-side-27 frontier).
- **Three novel 52-classes** beyond every catalogue, all ring-valid.
- **Bibliography corrected:** exact arXiv dates; Wang's 2603.07280
  title; Stapleton's initial (J.); Nielsen's name.

## Checklist

1. Commit everything; `git tag v2.0-ks51`; `git push origin master v2.0-ks51`.
2. `python3 matmul/zenodo_stage.py ks51 v2.0-ks51 v2.0`.
3. Zenodo → record 23305912 → New version → upload the staged files,
   apply the metadata changes above, add the version notes, Publish.
4. Record the new version DOI; put it in the paper's Artifacts
   paragraph if you want the PDF to cite its own version.
