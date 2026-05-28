# `tools/gbd/` — Global Benchmark Database integration

Scripts for downloading and curating SAT benchmarks from
[benchmark-database.de](https://benchmark-database.de) (the GBD project,
[Iser & Jabs 2024](https://doi.org/10.4230/LIPIcs.SAT.2024.18)).

Goal: maintain a local set of *fast-running, certifiably-solvable* CNF
instances to use as a fitness suite for matrix-backend evolution
experiments.

### Hard-guarantee UNSAT verification

CaDiCaL's verdict is enough for routine curation (Step 4 below), but
for **soundness guarantees** on UNSAT records — e.g., when you plan to
use those instances as a fitness function during evolution and a
backend's "UNSAT" verdict needs to be checkable against a gold
standard — there's a follow-up tool that runs an independent DRAT
checker:

```bash
# One-time install of cadical (brew) + drat-trim (clone+make).
brew install cadical
git clone https://github.com/marijnheule/drat-trim.git ~/projects/drat-trim
( cd ~/projects/drat-trim && make )

# Then verify all UNSAT records in the index:
tools/gbd/verify_unsat.py --timeout 60 --parallel 4
```

`verify_unsat.py` reads `curated.jsonl`, regenerates a DRAT proof via
standalone `cadical`, replays it through `drat-trim`, and updates
each UNSAT record with:

```json
{ "drat_verified": true,
  "drat_cadical_ms": 8942.9, "drat_trim_ms": 7748.8,
  "drat_proof_bytes": 31996589, "drat_lemmas": 6577 }
```

If the proof fails to verify, you'll see `WRONG-UNSAT` in the run
output and `drat_verified: false` in the record — that means the
original CaDiCaL verdict was wrong (extremely rare for cadical 3.0;
flag if it happens). Idempotent: re-running skips already-verified
records unless `--refresh` is passed.

## Environment variables

Three vars control file locations:

| Var | Purpose | Default |
|-----|---------|---------|
| `BENCH_DIR` | "base" — fallback for CNF_DIR + GBD_DIR + default index location | `/Users/greg/projects/sat_benchmarks` |
| `CNF_DIR` | where the `.cnf.xz` instances live | `$BENCH_DIR` |
| `GBD_DIR` | where `meta.db` + `base.db` live | `$BENCH_DIR/.gbd` |

In the common case (everything in one tree) just set `BENCH_DIR` and
both others derive from it. To split — e.g., share one CNF cache
across multiple curated indices in different dirs — set them
individually:

```bash
# Shared cache + DBs, project-specific index file:
export CNF_DIR=/Users/greg/projects/sat_benchmarks
export GBD_DIR=/Users/greg/projects/sat_benchmarks/.gbd
tools/gbd/curate.py --query "..." \
    --index /Users/greg/projects/my_project/curated.jsonl
```

If `GBD_DIR` doesn't have `meta.db` + `base.db`, curate.py errors out
immediately with a clear message — it used to hang on an interactive
prompt from the underlying `gbd` tool.

## Quickstart

```bash
# 1. One-time setup: install gbd-tools + download metadata DBs
tools/gbd/setup.sh

# 2. Explore the database with arbitrary queries
tools/gbd/query.sh "track=main_2025 and result=unsat" -r filename | head

# 3. Download instances matching a query (skips ones already on disk)
tools/gbd/download.sh "track=main_2025 and variables<2000" --dry-run

# 4. Curate: run CaDiCaL on candidates, keep ones it solves quickly,
#    save the verified verdict + runtime to a JSONL index
cargo build --release --bin sat        # curate.py needs target/release/sat
tools/gbd/curate.py --query "track=main_2025" --timeout 10 --parallel 8
```

After step 4, `$BENCH_DIR/curated.jsonl` (default
`/Users/greg/projects/sat_benchmarks/curated.jsonl`) contains one
record per instance:

```json
{"hash": "00d5a43a481477fa4d56a2ce152a6cfb", "filename": "...",
 "xz_path": "...", "nvars": 1234, "nclauses": 5678,
 "status": "SAT", "time_ms": 234.5, "assignment_verified": true,
 "checked_utc": "2026-05-26T19:50:12Z"}
```

`status` is `SAT`, `UNSAT`, `TIMEOUT`, or `ERROR`. SAT records carry an
`assignment_verified` flag (we re-evaluate the CaDiCaL assignment
against every CNF clause). UNSAT records trust CaDiCaL's verdict
(consider re-verifying with DRAT for higher confidence).

## Script reference

### `setup.sh`

One-time install. Idempotent.

- Installs `gbd-tools` via `pip3 --user`.
- Downloads `meta.db` (~30 MB; provides `track`, `result`, `family`,
  `filename`, `isohash`) and `base.db` (~20 MB; provides `variables`,
  `clauses`, balance/horn/graph metrics) into `$GBD_DIR`
  (= `$BENCH_DIR/.gbd` by default).
- Prints the `export GBD_DB=...` line you need for direct `gbd` use.

### `query.sh "<query>" [gbd-options...]`

Wrapper that sets `PATH` and `GBD_DB` for you, then calls `gbd get`.
Useful for one-off exploration without polluting your shell rc.

Common features to query on:

| Source | Feature | Examples |
|--------|---------|----------|
| meta | `track` | `main_2025`, `anni_2022`, `application_2016` |
| meta | `result` | `sat`, `unsat`, `unknown` |
| meta | `family` | `crypto`, `php`, `cliquecoloring`, `RoundRobin`, ... |
| meta | `filename` | use with `like` for prefix/infix match |
| base | `variables`, `clauses` | numeric filters |
| base | `minisat1m` | MiniSAT 1M-conflict runtime classifier |

Operators: `= != < > <= >= like unlike`. Combine with `and`, `or`,
parens. Use `feature like prefix%` / `like %suffix` / `like %infix%`.

### `download.sh "<query>" [--limit N] [--dry-run]`

1. Asks `benchmark-database.de/getinstances?query=...` for a wget-
   compatible `.uri` file listing all matching instance URLs.
2. Skips any whose hash already has a `<hash>-*.cnf.xz` in `$BENCH_DIR`.
3. Fetches the rest in parallel via `wget --content-disposition`
   (default 4 workers).

`--dry-run` just prints what would be fetched.

### `curate.py`

The substantive step. Per candidate instance:

1. Decompress (`xz -d -k`) into temp `.cnf`.
2. Run `target/release/sat --backend cadical -t TIMEOUT < instance.cnf`.
3. On `SAT`: parse the `v ... 0` assignment, **verify by direct
   evaluation against every clause** (full-strength check, no
   trust in CaDiCaL).
4. On `UNSAT`: record CaDiCaL's verdict + runtime (no proof check
   by default — run `verify_unsat.py` separately for that).
5. On `TIMEOUT` / `ERROR`: record the outcome but no time.
6. Append a JSON line to the index file. Clean up the temp `.cnf`.

Key flags:

| Flag | Default | Purpose |
|------|---------|---------|
| `--query QUERY` | `track=main_2025` | which GBD candidates to consider |
| `--timeout SECS` | `10` | CaDiCaL budget per instance |
| `--parallel N` | `4` | concurrent solver workers |
| `--max-instances N` | `0` (no limit) | cap candidates |
| `--index PATH` | `$BENCH_DIR/curated.jsonl` | output index location |
| `--refresh` | off | re-solve instances already in the index |
| `--include-sat-assignments` | off | keep the full `v` line in records |
| `--verify-unsat` | off | chain DRAT verification for each UNSAT result (writes `drat_verified` + timing inline; same effect as a follow-up `verify_unsat.py` run) |
| `--verify-timeout SECS` | `60` | per-instance budget for DRAT emission + verification (`--verify-unsat` only) |
| `--cadical-bin PATH` | from `$PATH` | standalone cadical binary (`--verify-unsat` only) |
| `--drat-trim-bin PATH` | `~/projects/drat-trim/drat-trim` | drat-trim binary (`--verify-unsat` only) |
| `--keep-proofs` | off | retain `.drat` files for audit (`--verify-unsat` only) |
| `--proofs-dir PATH` | `$BENCH_DIR/drat_proofs` | where `--keep-proofs` puts them |

The index file is **append-only by default**, so multiple runs against
different queries / time budgets accumulate. Use `--index PATH` to
maintain parallel suites (e.g., `curated_1s.jsonl`,
`curated_10s.jsonl`).

### `verify_unsat.py`

DRAT cross-check for the UNSAT records (`curate.py` trusts CaDiCaL's
verdict; this script re-derives it against an independent checker).
Run anytime; updates the existing index in place.

Per UNSAT record:

1. Decompress the `.cnf`.
2. Run standalone `cadical <cnf> <proof.drat> --no-binary -t TIMEOUT`
   to generate a DRAT proof of unsatisfiability.
3. Run `drat-trim <cnf> <proof.drat>` to **independently verify** the
   proof.
4. On success: write `drat_verified: true` into the record, along with
   `drat_cadical_ms` (proof emission time), `drat_trim_ms`
   (verification time), `drat_proof_bytes`, `drat_lemmas` (core lemma
   count from drat-trim).
5. On failure: `drat_verified: false` + `drat_error: <reason>`.

**Dependencies** (one-time):

```bash
brew install cadical        # standalone solver with --proof flag
git clone https://github.com/marijnheule/drat-trim.git ~/projects/drat-trim
( cd ~/projects/drat-trim && make )  # builds drat-trim binary
```

If either is missing, the script aborts with a clear message.

Key flags:

| Flag | Default | Purpose |
|------|---------|---------|
| `--index PATH` | `$BENCH_DIR/curated.jsonl` | which index to verify |
| `--timeout SECS` | `60` | per-instance budget for emission + verification |
| `--parallel N` | `4` | concurrent workers |
| `--refresh` | off | re-verify records already flagged `drat_verified=true` |
| `--keep-proofs` | off | retain `.drat` files (large; default deletes them) |
| `--proofs-dir PATH` | `$BENCH_DIR/drat_proofs` | where to keep proofs when `--keep-proofs` is on |
| `--cadical PATH` | from `$PATH` | override cadical binary |
| `--drat-trim PATH` | `~/projects/drat-trim/drat-trim` | override drat-trim binary |

Idempotent: re-running skips already-verified records.  Use
`--refresh` to re-check (e.g., after upgrading cadical or drat-trim).

**Watch for**: a `WRONG-UNSAT` outcome would mean CaDiCaL claimed UNSAT
on an instance whose DRAT proof failed to verify — almost certainly a
soundness bug worth investigating.  CaDiCaL 3.0 has had decades of
hardening so this is extremely rare in practice, but the script
surfaces it explicitly so you don't miss it.

## One-shot: curate + verify in a single pass

If you want the index to be fully verified (SAT direct + UNSAT DRAT)
straight from one command:

```bash
# Once: install the DRAT toolchain (cadical + drat-trim — see Quickstart).
# Then:
tools/gbd/curate.py \
    --query "track=main_2025 and minisat1m=yes" \
    --timeout 10 --parallel 8 \
    --verify-unsat --verify-timeout 60 \
    --index $BENCH_DIR/curated.jsonl
```

Every record lands with the right verification field already:

- SAT → `assignment_verified: true` (cheap, always done).
- UNSAT → `drat_verified: true` + timing/proof-size stats (slower).
- TIMEOUT / ERROR → neither.

This is equivalent to running `curate.py` then `verify_unsat.py` as
two separate steps, but each instance's DRAT verification happens in
the same parallel worker that solved it (one less process-pool
round-trip, one less .cnf decompress/cleanup cycle).

When to prefer two-pass:
- You want curation cheap *now* and verification deferred to overnight.
- You want to use different `--parallel` counts for the two phases
  (verification is often memory-heavier; fewer workers helps).
- You want to re-verify existing records without re-running CaDiCaL
  (just run `verify_unsat.py --refresh`).

## Curating multiple time-tier suites

For evolution fitness loops, you typically want a fast tier plus a
broader confirmation set. Idiomatic invocation:

```bash
# Fast tier (1s): tight feedback for inner-loop fitness eval.
tools/gbd/curate.py --query "track=main_2025" \
    --timeout 1 --parallel 10 \
    --index $BENCH_DIR/curated_1s.jsonl

# Medium tier (10s): the default, broader coverage for selection.
tools/gbd/curate.py --query "track=main_2025" \
    --timeout 10 --parallel 8 \
    --index $BENCH_DIR/curated_10s.jsonl

# Slow tier (60s, smaller set): final-confirmation eval, restricted to
# instances MiniSAT solved within 1M conflicts (= GBD's "easy" tag).
tools/gbd/curate.py --query "track=main_2025 and minisat1m=yes" \
    --timeout 60 --parallel 4 \
    --index $BENCH_DIR/curated_60s.jsonl
```

(The `minisat1m=yes` predicate uses GBD's pre-computed boolean feature
for "solvable by MiniSAT in 1M conflicts", a strong proxy for "easy"
that we don't have to test ourselves. Values are `yes` / `no`.)

### `run_benchmark.py`

Once you have a curated index, `run_benchmark.py` runs an arbitrary
`sat` backend against every problem in it, in parallel, with a live
multi-worker progress display, and incrementally builds a Markdown
report (summary table + cactus plot) updated as each result lands.

Per-instance pipeline mirrors `doc/competition-benchmarks.sh` (decompress
→ run sat → parse → atomic-append row → re-finalize) but adds:

- **JSONL-driven**: processes records from a curated index, not "every
  .cnf.xz in a directory".  Lets you target a fitness suite without
  pulling in TIMEOUT instances or instances you haven't curated yet.
- **Cross-check** against the record's known `status`: a SAT/UNSAT
  disagreement is logged as `MISMATCH` (separate summary row, excluded
  from the cactus curve, exit code 1 — these are soundness bugs).
- **Live TUI**: each worker gets a fixed terminal row that shows its
  current `sat --progress` frame (e.g. `c CaDiCaL: 4.8K learned 0.1s`).
  Scrollback above the worker block accumulates "done" lines.  Falls
  back to one-line completion logs on non-TTY stderr or `--no-progress`.

```bash
# Run cadical with 60s timeout, 4 workers, against the default index
tools/gbd/run_benchmark.py --index $BENCH_DIR/curated.jsonl

# Compare matrix backends on the same suite at 30s
tools/gbd/run_benchmark.py --index easy.jsonl -b eff -t 30 -j 8
tools/gbd/run_benchmark.py --index easy.jsonl -b greedy_eff -t 30 -j 8

# Only the SAT instances, with sat preprocessing forced off
tools/gbd/run_benchmark.py --index curated.jsonl \
    --filter "r['status'] == 'SAT'" --no-preprocess

# Pass extra args through to sat (repeatable)
tools/gbd/run_benchmark.py --index curated.jsonl \
    --sat-arg --emit-drat --sat-arg /tmp/last-proof.drat
```

Key flags:

| Flag | Default | Purpose |
|------|---------|---------|
| `--index PATH` | (required) | curate.py JSONL output file |
| `-b NAME` / `--backend` | `cadical` | sat backend name |
| `-t SECS` / `--timeout` | `60` | per-instance wall-clock budget |
| `-j N` / `--parallel` | `4` | concurrent workers |
| `--preprocess` / `--no-preprocess` | sat default | forward to sat |
| `-o PATH` / `--output` | auto-named in `doc/` | output .md path |
| `--limit N` | 0 (no limit) | only process first N matching records |
| `--filter EXPR` | none | Python expr on record dict `r`, e.g. `"r['nvars']<1000"` |
| `--no-progress` | auto on non-TTY | disable the live TUI |
| `--finalize-interval SECS` | `2.0` | min seconds between summary + plot regens |
| `--sat-arg ARG` | (none, repeatable) | extra args forwarded to sat verbatim |

The output filename encodes the backend + timeout + preproc setting
(`doc/competition-benchmark_<index-stem>_<timeout>_<backend>[_pp|_nopp].md`)
and auto-numbers (`_2`, `_3`, …) so consecutive runs don't clobber.

Exit code: `0` on success, `1` if any MISMATCH was recorded, `2` for
preflight failures (missing binary, missing index, etc.).

## See also

- [GBD homepage](https://benchmark-database.de)
- [GBD source code](https://github.com/Udopia/gbd)
- [Iser & Jabs, SAT 2024 paper](https://doi.org/10.4230/LIPIcs.SAT.2024.18)
- `doc/competition-benchmarks.sh` — runs an arbitrary backend across
  the full local CNF directory (uses `BENCH_DIR` env var the same way).
- `doc/competition-benchmarks-plot.py` — the cactus plotter
  `run_benchmark.py` shells out to for the PNG inside the .md report.
- `target/release/sat --backend cadical` — what curate.py invokes
  per instance to get the authoritative verdict.
