#!/usr/bin/env python3
"""
Build a curated index balanced across benchmark families.

Why this exists: the natural GBD distribution is heavily skewed —
~30% of instances live in 3 families (station-repacking, uniform-
random, agile), while ~100 long-tail families have <50 instances each.
A query like `minisat1m=yes and variables<2000` returns mostly
station-repacking and uniform-random — giving you no signal on the
structural-cardinality families (pigeon-hole, tseitin-formulas,
coloring-mycielski, waerden, …) where matrix-method / eff backends
are theoretically strongest.  This tool fixes that by hard-capping
per-family contribution before download / curation.

Workflow:
  1. SQL-join meta.db + base.db (no `gbd` CLI dependency) to find
     candidates matching --base-query.
  2. Group by `family`; rank families by candidate count; keep the
     top --top-families.
  3. Within each family, sort candidates by ascending `variables`
     (smallest = fastest = most fitness-loop-friendly) and take
     up to --per-family.
  4. --download (default ON): fetch any missing .cnf.xz from GBD's
     /file/<hash> endpoint, in parallel.  Idempotent: skips
     already-on-disk files.
  5. --curate (default ON): solve each sampled instance with
     CaDiCaL (default 30s budget), verify, and append to --index.
     Reuses tools/gbd/curate.py's solve_one — same JSONL schema,
     same SAT-assignment direct-eval, same dedupe semantics.

Output: a JSONL index of solved+verified instances, balanced across
the requested families.

Usage:
  # Default: 12 families × 10 instances = ~120 candidate suite
  tools/gbd/curate_balanced.py --index $BENCH_DIR/curated_balanced.jsonl

  # Bigger, slower suite
  tools/gbd/curate_balanced.py --top-families 20 --per-family 20 \\
      --timeout 60 --index $BENCH_DIR/curated_balanced_big.jsonl

  # Specific families instead of auto-top
  tools/gbd/curate_balanced.py \\
      --families agile,pigeon-hole,tseitin-formulas,coloring,scheduling,hamiltonian \\
      --per-family 15

  # Plan only (no download, no curate) — shows what would be picked
  tools/gbd/curate_balanced.py --plan-only
"""

import argparse
import json
import os
import sqlite3
import subprocess
import sys
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# Reuse curate.py's environment + solve_one machinery so the JSONL
# schema is identical and we automatically benefit from any
# improvements to solve_one (DRAT verification chain, assignment
# verification, etc.).
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from curate import (  # type: ignore
    BENCH_DIR, CNF_DIR, GBD_DIR, SAT_BIN,
    solve_one, find_cnf, dedupe_index_file,
)

DEFAULT_INDEX = BENCH_DIR / "curated_balanced.jsonl"


# ---------------------------------------------------------------------------
# SQL: pick candidates from the GBD metadata
# ---------------------------------------------------------------------------
def open_gbd() -> sqlite3.Connection:
    """Open meta.db with base.db ATTACHED.  Same join-on-hash semantics
    as `gbd get`, but in-process so we can do per-family sampling
    without round-tripping through the CLI."""
    meta = GBD_DIR / "meta.db"
    base = GBD_DIR / "base.db"
    if not meta.exists() or not base.exists():
        print(f"FATAL: meta.db + base.db not found in {GBD_DIR}\n"
              f"       Run tools/gbd/setup.sh first.", file=sys.stderr)
        sys.exit(2)
    conn = sqlite3.connect(str(meta))
    conn.execute(f"ATTACH DATABASE '{base}' AS base")
    return conn


def fetch_candidates(
    conn: sqlite3.Connection,
    max_vars: int,
    max_clauses: int,
    minisat1m_only: bool,
    extra_sql_where: Optional[str],
) -> List[Dict[str, str]]:
    """
    Return all candidates matching the base filter, as a list of dicts
    with hash / filename / family / variables / clauses.

    Filter is built in SQL (not via the GBD query language) so we can
    easily extend it with arbitrary SQL predicates via
    `extra_sql_where`.  All non-integer columns are TEXT in GBD's
    schema; we CAST `variables` / `clauses` to INTEGER for numeric
    comparison.
    """
    where = []
    params: List = []
    if max_vars > 0:
        where.append("CAST(base.features.variables AS INTEGER) <= ?")
        params.append(max_vars)
    if max_clauses > 0:
        where.append("CAST(base.features.clauses AS INTEGER) <= ?")
        params.append(max_clauses)
    if minisat1m_only:
        where.append("main.features.minisat1m = 'yes'")
    # Always require a non-empty family (else we can't bucket).
    where.append("main.features.family IS NOT NULL")
    where.append("main.features.family != ''")
    if extra_sql_where:
        where.append(f"({extra_sql_where})")
    where_clause = " AND ".join(where) if where else "1=1"
    # Friendly filename trick: GBD stores `features.filename` defaulted
    # to the hash itself, and keeps the *actual* human-readable names
    # (e.g. `php-010-010.shuffled-as.sat05-1157.cnf.xz`) in a separate
    # `filename` table — one hash can map to several alias names (the
    # same CNF showing up in different competitions / archives).  We
    # pull one such alias via a correlated subquery and fall back to
    # `features.filename` only if the join finds nothing.  Without
    # this fall-back, agile / pigeon-hole / etc. show up as raw
    # 32-hex hashes in every report and downstream index, defeating
    # human readability.
    sql = f"""
        SELECT
          main.features.hash      AS hash,
          COALESCE(
            (SELECT value FROM main.filename
                WHERE main.filename.hash = main.features.hash
                ORDER BY value LIMIT 1),
            main.features.filename
          ) AS filename,
          main.features.family    AS family,
          main.features.result    AS result,
          CAST(base.features.variables AS INTEGER) AS variables,
          CAST(base.features.clauses  AS INTEGER) AS clauses
        FROM main.features
        JOIN base.features ON base.features.hash = main.features.hash
        WHERE {where_clause}
    """
    rows = []
    for r in conn.execute(sql, params):
        # filename can still be a comma-joined alias list for some
        # records — split-and-take-first in case the table has them.
        fname = (r[1] or "").split(",", 1)[0]
        rows.append({
            "hash":      r[0],
            "filename":  fname,
            "family":    r[2],
            "result":    r[3] or "unknown",
            "variables": r[4] or 0,
            "clauses":   r[5] or 0,
        })
    return rows


# ---------------------------------------------------------------------------
# Sampling
# ---------------------------------------------------------------------------
def sample_balanced(
    candidates: List[Dict],
    families: Optional[List[str]],
    top_families: int,
    per_family: int,
    sat_unsat_balance: bool,
) -> List[Dict]:
    """
    Bucket candidates by family; keep at most `per_family` per bucket.
    Within a bucket, prefer:
      - if `sat_unsat_balance`: alternate SAT / UNSAT picks for a
        roughly even split per family (falls back to whichever exists).
      - else: smallest `variables` first (= fastest to solve).

    If `families` is set, only those buckets are kept (in that order).
    Otherwise, the `top_families` largest buckets are kept (ranked by
    candidate count desc).
    """
    buckets: Dict[str, List[Dict]] = {}
    for c in candidates:
        buckets.setdefault(c["family"], []).append(c)

    if families is not None:
        kept_fams = [f for f in families if f in buckets]
        missing_fams = [f for f in families if f not in buckets]
        if missing_fams:
            print(f"warning: no candidates for families {missing_fams} "
                  f"under the current --base-query", file=sys.stderr)
    else:
        # Rank families by raw candidate count, take top N.
        kept_fams = sorted(buckets, key=lambda f: -len(buckets[f]))[:top_families]

    picked: List[Dict] = []
    for fam in kept_fams:
        bucket = buckets[fam]
        if sat_unsat_balance:
            sat   = sorted([c for c in bucket if c["result"] == "sat"],
                           key=lambda c: c["variables"])
            unsat = sorted([c for c in bucket if c["result"] == "unsat"],
                           key=lambda c: c["variables"])
            other = sorted([c for c in bucket if c["result"] not in ("sat", "unsat")],
                           key=lambda c: c["variables"])
            half = per_family // 2
            chosen = sat[:half] + unsat[:half]
            # If one side is short, fill from the other / other.
            if len(chosen) < per_family:
                remaining = per_family - len(chosen)
                pool = (sat[half:] + unsat[half:] + other)
                chosen += pool[:remaining]
        else:
            chosen = sorted(bucket, key=lambda c: c["variables"])[:per_family]
        picked.extend(chosen)
    return picked


# ---------------------------------------------------------------------------
# Download missing CNFs from GBD
# ---------------------------------------------------------------------------
def gbd_download_url(hash_: str) -> str:
    """GBD's per-instance download endpoint.  Returns a .cnf.xz with a
    Content-Disposition that wget honors as `<hash>-<filename>.cnf.xz`."""
    return f"https://benchmark-database.de/file/{hash_}"


def download_one(hash_: str, dest_dir: Path) -> Tuple[str, bool, str]:
    """Wget a single instance.  Returns (hash, success, message)."""
    url = gbd_download_url(hash_)
    # Use wget for Content-Disposition handling (GBD names files
    # <hash>-<original>.cnf.xz via that header).
    try:
        result = subprocess.run(
            ["wget", "-q", "--content-disposition", "-P", str(dest_dir), url],
            capture_output=True, text=True, timeout=180,
        )
        if result.returncode != 0:
            return (hash_, False, result.stderr.strip()[:200] or "wget non-zero exit")
        return (hash_, True, "")
    except subprocess.TimeoutExpired:
        return (hash_, False, "download timeout (180s)")
    except Exception as e:
        return (hash_, False, f"{type(e).__name__}: {e}")


def download_missing(picked: List[Dict], parallel: int) -> Tuple[int, int]:
    """Download any sampled instances not yet in CNF_DIR.  Returns
    (downloaded_count, failed_count)."""
    missing = [p for p in picked if find_cnf(p["hash"]) is None]
    if not missing:
        print(f"all {len(picked)} sampled instances already on disk")
        return (0, 0)
    print(f"downloading {len(missing)} missing instances "
          f"(parallel={parallel})...")
    CNF_DIR.mkdir(parents=True, exist_ok=True)
    ok = fail = 0
    with ThreadPoolExecutor(max_workers=parallel) as ex:
        futures = {ex.submit(download_one, p["hash"], CNF_DIR): p for p in missing}
        for i, fut in enumerate(as_completed(futures), 1):
            p = futures[fut]
            h, success, err = fut.result()
            if success:
                ok += 1
                # Don't spam — only print every 10th or last.
                if i % 10 == 0 or i == len(missing):
                    print(f"  [{i:4}/{len(missing)}] downloaded ({ok} ok, {fail} failed)")
            else:
                fail += 1
                print(f"  ! [{p['family']}/{p['filename']}] download failed: {err}",
                      file=sys.stderr)
    return (ok, fail)


# ---------------------------------------------------------------------------
# Curate the sampled set (reuses curate.py's solve_one)
# ---------------------------------------------------------------------------
def curate_picked(
    picked: List[Dict], timeout: int, parallel: int,
    index_path: Path, refresh: bool, include_assignments: bool,
    drat_cfg: Optional[dict],
) -> None:
    """Solve each sampled instance and append to index.  Mirrors
    curate.py's main solve loop but operates on a pre-sampled list
    instead of a `--query` candidate pool."""
    from concurrent.futures import ProcessPoolExecutor as PPE

    # Load existing index to honor --refresh semantics.
    from curate import load_index  # type: ignore
    index = load_index(index_path) if index_path.exists() else {}

    queue = []
    skipped = on_disk = 0
    for p in picked:
        xz = find_cnf(p["hash"])
        if not xz:
            continue  # download failed and we proceed without
        on_disk += 1
        if not refresh and p["hash"] in index:
            skipped += 1
            continue
        queue.append((p["hash"], p["filename"], xz, timeout, drat_cfg))

    print()
    print(f"sampled instances:   {len(picked)}")
    print(f"on disk:             {on_disk}")
    print(f"already in index:    {skipped}  (use --refresh to re-solve)")
    print(f"to solve:            {len(queue)}")
    if not queue:
        return

    print(f"running cadical with {timeout}s budget, parallel={parallel}...")
    print()

    n_sat = n_unsat = n_to = n_err = 0
    with index_path.open("a") as fout, PPE(max_workers=parallel) as ex:
        futures = {ex.submit(solve_one, item): item for item in queue}
        for i, fut in enumerate(as_completed(futures), 1):
            item = futures[fut]
            try:
                rec = fut.result()
            except Exception as e:
                rec = {"hash": item[0], "filename": item[1],
                       "status": "WORKER_ERROR", "error": str(e)}
            status = rec.get("status", "?")
            if status == "SAT": n_sat += 1
            elif status == "UNSAT": n_unsat += 1
            elif status in ("TIMEOUT", "WALL_TIMEOUT"): n_to += 1
            else: n_err += 1

            if not include_assignments and "assignment" in rec:
                rec.pop("assignment", None)

            fout.write(json.dumps(rec) + "\n")
            fout.flush()
            elapsed = rec.get("time_ms")
            tag = f"{elapsed:7.1f}ms" if elapsed is not None else "      -"
            drat_tag = ""
            if "drat_verified" in rec:
                drat_tag = "  DRAT✓" if rec["drat_verified"] is True else "  DRAT✗"
            print(f"[{i:4}/{len(queue)}] {status:7}  {tag}{drat_tag}  {item[1]}")

    print()
    print("=== solve summary ===")
    print(f"  SAT:     {n_sat}")
    print(f"  UNSAT:   {n_unsat}")
    print(f"  TIMEOUT: {n_to}")
    print(f"  ERROR:   {n_err}")

    # Auto-dedupe (same policy as curate.py).
    before, after = dedupe_index_file(index_path)
    if before != after:
        print(f"deduped index: {before} → {after} rows "
              f"({before - after} duplicate-hash records collapsed)")


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------
def report_plan(picked: List[Dict]) -> None:
    """Print a per-family breakdown of what would be curated."""
    print()
    print("=== sample plan ===")
    print(f"{'family':<35} {'count':>6} {'sat':>4} {'unsat':>5} "
          f"{'unk':>4} {'min vars':>9} {'max vars':>9}")
    by_fam: Dict[str, List[Dict]] = {}
    for p in picked:
        by_fam.setdefault(p["family"], []).append(p)
    for fam in sorted(by_fam, key=lambda f: -len(by_fam[f])):
        bucket = by_fam[fam]
        sats = sum(1 for c in bucket if c["result"] == "sat")
        unsats = sum(1 for c in bucket if c["result"] == "unsat")
        unks = len(bucket) - sats - unsats
        vmin = min(c["variables"] for c in bucket)
        vmax = max(c["variables"] for c in bucket)
        print(f"  {fam:<33} {len(bucket):>6} {sats:>4} {unsats:>5} "
              f"{unks:>4} {vmin:>9} {vmax:>9}")
    print(f"  {'TOTAL':<33} {len(picked):>6} "
          f"{sum(1 for p in picked if p['result']=='sat'):>4} "
          f"{sum(1 for p in picked if p['result']=='unsat'):>5} "
          f"{sum(1 for p in picked if p['result'] not in ('sat','unsat')):>4}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    # Selection
    ap.add_argument("--families", default=None,
                    help="Comma-separated family names to include "
                         "(default: auto-pick the --top-families largest).")
    ap.add_argument("--top-families", type=int, default=12,
                    help="When --families is not set, auto-pick the N "
                         "largest families that have at least 1 candidate "
                         "(default: %(default)s).")
    ap.add_argument("--per-family", type=int, default=10,
                    help="Max instances per family in the curated set "
                         "(default: %(default)s).")
    ap.add_argument("--max-vars", type=int, default=2000,
                    help="Filter: max variable count per instance "
                         "(0 = unlimited; default: %(default)s).")
    ap.add_argument("--max-clauses", type=int, default=15000,
                    help="Filter: max clause count per instance "
                         "(0 = unlimited; default: %(default)s).")
    ap.add_argument("--minisat1m", default="yes",
                    choices=("yes", "no", "any"),
                    help="Filter on GBD's minisat1m feature (MiniSAT "
                         "solved within 1M conflicts).  Default 'yes' = "
                         "easy instances only.  Use 'any' to include "
                         "instances with no minisat1m feature.")
    ap.add_argument("--extra-sql-where", default=None,
                    help="Raw SQL WHERE clause appended to the candidate "
                         "filter, e.g. \"main.features.track LIKE 'anni_%%'\".  "
                         "Advanced — see schema in meta.db / base.db.")
    ap.add_argument("--no-sat-unsat-balance", action="store_true",
                    help="Pick smallest-variables-first within each family "
                         "instead of trying to balance SAT/UNSAT (which "
                         "matters for evolution-fitness suites that need "
                         "both result classes).")

    # Pipeline control
    ap.add_argument("--no-download", action="store_true",
                    help="Skip the download step.  Curate only instances "
                         "already on disk in CNF_DIR; missing ones are "
                         "silently dropped from the sample.")
    ap.add_argument("--no-curate", action="store_true",
                    help="Skip the curate step.  Stop after planning + "
                         "(optionally) downloading; useful for staging a "
                         "big download overnight before solving.")
    ap.add_argument("--plan-only", action="store_true",
                    help="Just show the sample plan and exit.  Implies "
                         "both --no-download and --no-curate.")
    ap.add_argument("--download-parallel", type=int, default=4,
                    help="Concurrent wget workers (default: %(default)s).")

    # Solve params (passed to curate.solve_one)
    ap.add_argument("--timeout", type=int, default=30,
                    help="CaDiCaL budget per instance, seconds (default: %(default)s).")
    ap.add_argument("--parallel", type=int, default=4,
                    help="Concurrent solver workers (default: %(default)s).")
    ap.add_argument("--index", default=str(DEFAULT_INDEX),
                    help="Output JSONL path (default: %(default)s).")
    ap.add_argument("--refresh", action="store_true",
                    help="Re-solve instances already in the index.")
    ap.add_argument("--include-sat-assignments", action="store_true",
                    help="Keep full v-line assignments in records.")

    args = ap.parse_args()

    if args.plan_only:
        args.no_download = True
        args.no_curate = True

    # ── Query ──
    conn = open_gbd()
    candidates = fetch_candidates(
        conn,
        max_vars=args.max_vars,
        max_clauses=args.max_clauses,
        minisat1m_only=(args.minisat1m == "yes"),
        extra_sql_where=args.extra_sql_where,
    )
    print(f"candidates (after filter): {len(candidates)}")
    if not candidates:
        print("FATAL: 0 candidates — relax --max-vars / --max-clauses or "
              "--minisat1m.", file=sys.stderr)
        return 1

    # ── Sample ──
    requested_families = (
        [f.strip() for f in args.families.split(",") if f.strip()]
        if args.families else None
    )
    picked = sample_balanced(
        candidates,
        families=requested_families,
        top_families=args.top_families,
        per_family=args.per_family,
        sat_unsat_balance=not args.no_sat_unsat_balance,
    )
    print(f"sampled (balanced):        {len(picked)}")
    report_plan(picked)

    if args.plan_only:
        return 0

    # ── Download ──
    if not args.no_download:
        ok, fail = download_missing(picked, args.download_parallel)
        if fail:
            print(f"warning: {fail} downloads failed; will curate only "
                  f"the {len(picked) - fail} successfully-on-disk ones",
                  file=sys.stderr)

    # ── Curate ──
    if not args.no_curate:
        if not SAT_BIN.exists():
            print(f"FATAL: sat binary missing: {SAT_BIN}\n"
                  f"       Build with: cargo build --release --bin sat",
                  file=sys.stderr)
            return 2
        curate_picked(
            picked, timeout=args.timeout, parallel=args.parallel,
            index_path=Path(args.index), refresh=args.refresh,
            include_assignments=args.include_sat_assignments,
            drat_cfg=None,  # add --verify-unsat plumbing later if desired
        )
        print(f"\nindex file: {args.index}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
