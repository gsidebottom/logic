# Zenodo new-version kit — 55-addition deposit, v1.1

Existing record: **doi:10.5281/zenodo.21240904** (v1.0-mm55, 2026-07-07).
Publish this as a **New version** of that record, so the concept DOI
keeps resolving to the latest version and v1.0 stays citable.

Stage the files from the deposit tag:

```
git tag v1.1-mm55
python3 matmul/zenodo_stage.py mm55 v1.1-mm55 v1.1
```

This writes `zenodo-upload-mm55-v1.1/` (gitignored).

## Files to upload

- `matmul_adds_paper.pdf` — the paper (October 2026 update)
- `i19-55adds-slp.txt`, `i19-perminov56.bits`, `verify_slp_file.py`,
  `mm55.rs` — the program, its representative, the independent
  verifier and the Rust transcription (unchanged from v1.0)
- `proof-lake-project.zip` — the Lean/Lake project (no `.lake`)
- `flat55-frontier.tar.gz` — new: the exact flat-floor tool
  (`src/floors.rs` + `src/bin/floors.rs`, `--exact-total`), the
  frontier pipeline (`cfloor.py`, `gf2min.py`, `flat55_frontier.py`)
  and `matmul/external/flat55/` (the 616-scheme frontier list and
  per-class results)
- `logic-mm55-v1.1.tar.gz` — full repository snapshot at the tag

## Metadata changes

**Version:** v1.1-mm55

**Publication date:** the day you publish

**Description:** append this paragraph to the v1.0 description:

October 2026 update: an exact orbit-wide computation of the F2 flat
minimum (three exact 168×168 side tables, the output side by
transposition, and a min-plus scan over all 168³ sandwiches) closes
the one region the original no-54 argument left open — the 616
database classes whose output side can reach 27. Every one has a flat
minimum of at least 56 except the record class itself (55). The record
class is therefore the only class in the Heule–Kauers–Seidl database
that attains 55. The same computation proves Sun's 56 and Perminov's
cn119 56 exactly optimal for their classes.

**Related identifiers (add):**

- `10.5281/zenodo.23305912` — is referenced by (the KS-51 deposit,
  which uses the same flat-floor computation)

## Changes since v1.0-mm55 (for the version notes)

- Results section: dated update closing the 616-class frontier — the
  record class is the unique 55-class in the database.
- Sun's class and Perminov's cn119 class: flat floor 56, attained, so
  both 56s are exactly optimal class-wide (v1.0 proved this only for
  slim-sided representatives).
- Abstract: dated update note; future-work item "more 55s" resolved.
- Reference list: list-formatting options no longer leak into the
  first entry's text.

## Checklist

1. Commit everything; `git tag v1.1-mm55`; `git push origin master v1.1-mm55`.
2. `python3 matmul/zenodo_stage.py mm55 v1.1-mm55 v1.1`.
3. Zenodo → record 21240904 → New version → upload, apply the metadata
   changes, add the version notes, Publish.
