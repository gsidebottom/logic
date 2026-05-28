#!/usr/bin/env python3
"""
Curate a fast-runnable, certifiably-solvable subset of GBD benchmarks.

Workflow per instance:
  1. Decompress the .cnf.xz (kept on disk; .cnf deleted after).
  2. Run `sat --backend cadical -t TIMEOUT` to get an authoritative
     verdict (SAT / UNSAT) plus runtime.
  3. On SAT: extract the satisfying assignment from the `v ... 0` line
     and verify by direct evaluation against the CNF clauses.
  4. On UNSAT: trust CaDiCaL's verdict (re-solving with DRAT proof
     would be heavier; CaDiCaL on instances that solve in <10s is
     near-certain to be correct).
  5. On TIMEOUT: skip — instance is too slow for the curated set.
  6. Append a row to the curated index (JSONL: one JSON object per
     line, easy to grep / partially read / append).

Re-runnable: the index file accumulates across runs.  Already-recorded
instances are skipped unless --refresh is passed.

Usage:
    curate.py [--query QUERY] [--timeout SECS] [--parallel N]
              [--max-instances N] [--index PATH] [--refresh]

Defaults curate ~100-200 instances that CaDiCaL solves in <10 s each.

Examples:
    # Curate from main_2025 with default 10s budget:
    tools/gbd/curate.py --query "track=main_2025"

    # Tighter budget (1s) for evolution fitness:
    tools/gbd/curate.py --timeout 1 --index sat_benchmarks/curated_1s.jsonl

    # Re-run on existing instances (e.g., to refresh timings):
    tools/gbd/curate.py --refresh
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import time
import datetime
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Optional, List, Tuple, Dict

# Allow `from verify_unsat import ...` so --verify-unsat can chain the
# DRAT verification step inline.  Both files live in the same dir.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_unsat import verify_one as drat_verify_one, DEFAULT_DRAT_TRIM

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SAT_BIN = REPO_ROOT / "target" / "release" / "sat"
# BENCH_DIR is the *base* — by default both CNFs and the .gbd DBs live
# under it.  For projects that want curation outputs separated from
# the CNF cache, set CNF_DIR (where .cnf.xz files are) and GBD_DIR
# (where meta.db + base.db live) explicitly.
BENCH_DIR = Path(os.environ.get("BENCH_DIR", "/Users/greg/projects/sat_benchmarks"))
CNF_DIR = Path(os.environ.get("CNF_DIR", BENCH_DIR))
GBD_DIR = Path(os.environ.get("GBD_DIR", BENCH_DIR / ".gbd"))
DEFAULT_INDEX = BENCH_DIR / "curated.jsonl"


def gbd_query(query: str) -> List[Tuple[str, str]]:
    """Run `gbd get` and return [(hash, filename), ...] for matches.

    Fails fast (no hang) if the GBD DBs aren't at GBD_DIR — otherwise
    the `gbd` subprocess would prompt interactively on stdin for
    "Database doesn't exist. Create new? [n]|y:" and block forever.
    """
    missing = [d for d in ("meta.db", "base.db") if not (GBD_DIR / d).exists()]
    if missing:
        print(f"FATAL: GBD database file(s) missing: "
              f"{', '.join(str(GBD_DIR / d) for d in missing)}", file=sys.stderr)
        print("  Either:", file=sys.stderr)
        print(f"    1. Set GBD_DIR to the directory holding meta.db + base.db, e.g.:",
              file=sys.stderr)
        print(f"         export GBD_DIR=/Users/greg/projects/sat_benchmarks/.gbd",
              file=sys.stderr)
        print(f"    2. Or run tools/gbd/setup.sh with the correct BENCH_DIR.",
              file=sys.stderr)
        sys.exit(2)
    env = os.environ.copy()
    env["GBD_DB"] = f"{GBD_DIR}/meta.db:{GBD_DIR}/base.db"
    # Make sure user-site bin is on PATH (where pip --user puts `gbd`).
    user_bin = subprocess.check_output(
        ["python3", "-c", "import site; print(site.getuserbase() + '/bin')"]
    ).decode().strip()
    env["PATH"] = f"{user_bin}:{env.get('PATH', '')}"

    out = subprocess.check_output(
        ["gbd", "get", query, "-r", "filename"],
        env=env, text=True
    )
    rows = []
    for line in out.splitlines():
        line = line.strip()
        if not line or line.startswith("Reading"):
            continue
        parts = line.split(None, 1)
        if len(parts) != 2:
            continue
        hash_, fname = parts
        # filename may carry multiple comma-separated values; take the first
        rows.append((hash_, fname.split(",")[0]))
    return rows


def find_cnf(hash_: str) -> Optional[Path]:
    """Locate the .cnf.xz file for a given hash in CNF_DIR."""
    matches = list(CNF_DIR.glob(f"{hash_}-*.cnf.xz"))
    return matches[0] if matches else None


def parse_assignment(cadical_stdout: str) -> Optional[List[int]]:
    """Extract `v ... 0` literals from CaDiCaL output, or None if not SAT."""
    lits = []
    in_v = False
    for line in cadical_stdout.splitlines():
        if line.startswith("v "):
            in_v = True
            for tok in line[2:].split():
                n = int(tok)
                if n == 0:
                    return lits
                lits.append(n)
        elif in_v:
            # `v` can span multiple lines; subsequent value lines start
            # with `v ` per DIMACS spec but our sat emits a single line.
            break
    return lits if lits else None


def verify_assignment(cnf_path: Path, assignment: List[int]) -> bool:
    """Evaluate the assignment against every clause in the CNF."""
    # Build a dict: var → bool
    asgn = {abs(l): (l > 0) for l in assignment}
    with open(cnf_path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in "cp%":
                continue
            lits = [int(t) for t in line.split() if t]
            # clauses end with 0; strip it
            if lits and lits[-1] == 0:
                lits = lits[:-1]
            if not lits:
                continue
            # Clause satisfied iff any lit is true under asgn
            sat = any(asgn.get(abs(l), False) == (l > 0) for l in lits)
            if not sat:
                return False
    return True


def solve_one(args: tuple) -> dict:
    """Per-instance worker.  Returns a dict suitable for the index.

    Tuple shape: (hash, filename, xz_path, timeout_s, drat_cfg_or_None).

    If drat_cfg is non-None, it's a dict matching verify_unsat.verify_one's
    `args` schema (cadical, drat_trim, timeout, proofs_dir, keep_proofs);
    on UNSAT verdicts we chain into the DRAT verifier inline so the
    record carries both the solve + verification stats in one pass.
    """
    hash_, filename, xz_path, timeout_s, drat_cfg = args
    # Decompress to a temp cnf next to the xz.
    cnf_path = Path(str(xz_path)[:-3])  # strip .xz
    cleanup = False
    if not cnf_path.exists():
        subprocess.run(["xz", "-d", "-k", str(xz_path)], check=True)
        cleanup = True

    result = {
        "hash": hash_,
        "filename": filename,
        "xz_path": str(xz_path),
        "checked_utc": datetime.datetime.utcnow().isoformat(timespec="seconds") + "Z",
    }
    # Capture size features from the CNF header.
    try:
        with open(cnf_path) as f:
            for line in f:
                if line.startswith("p cnf"):
                    parts = line.split()
                    result["nvars"] = int(parts[2])
                    result["nclauses"] = int(parts[3])
                    break
    except Exception as e:
        result["error"] = f"read p line: {e}"
        if cleanup: cnf_path.unlink(missing_ok=True)
        return result

    # Run sat --backend cadical with a hard timeout.
    t0 = time.time()
    try:
        proc = subprocess.run(
            [str(SAT_BIN), "--backend", "cadical", "-t", str(timeout_s)],
            stdin=open(cnf_path),
            capture_output=True, text=True,
            timeout=timeout_s + 5,
        )
    except subprocess.TimeoutExpired:
        result["status"] = "WALL_TIMEOUT"
        if cleanup: cnf_path.unlink(missing_ok=True)
        return result
    elapsed_ms = (time.time() - t0) * 1000.0

    out = proc.stdout + proc.stderr
    if "c TIMEOUT" in out:
        result["status"] = "TIMEOUT"
    elif "s SATISFIABLE" in out:
        result["status"] = "SAT"
        result["time_ms"] = elapsed_ms
        asgn = parse_assignment(out)
        if asgn is None:
            result["assignment_verified"] = False
            result["error"] = "no v line"
        else:
            result["assignment"] = asgn
            result["assignment_verified"] = verify_assignment(cnf_path, asgn)
    elif "s UNSATISFIABLE" in out:
        result["status"] = "UNSAT"
        result["time_ms"] = elapsed_ms
        # Chain into DRAT verification if requested.  We keep the .cnf
        # alive for verify_one; it'll reuse the same decompressed file.
        if drat_cfg is not None:
            verify_args = dict(drat_cfg)
            verify_args["hash"] = hash_
            verify_args["xz_path"] = str(xz_path)
            try:
                _, drat_update = drat_verify_one(verify_args)
                result.update(drat_update)
            except Exception as e:
                result["drat_verified"] = "error"
                result["drat_error"] = f"verify_one exception: {e}"
    else:
        result["status"] = "ERROR"
        result["error"] = (out[-500:] if out else "(no output)")

    if cleanup:
        cnf_path.unlink(missing_ok=True)
    return result


def load_index(path: Path) -> Dict[str, dict]:
    """Load existing index keyed by hash."""
    if not path.exists():
        return {}
    out = {}
    with open(path) as f:
        for line in f:
            try:
                obj = json.loads(line)
                out[obj["hash"]] = obj
            except Exception:
                pass
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--query", default="track=main_2025",
                    help="GBD query for candidate instances "
                         "(default: %(default)s)")
    ap.add_argument("--timeout", type=int, default=10,
                    help="CaDiCaL time budget per instance, seconds "
                         "(default: %(default)s)")
    ap.add_argument("--parallel", type=int, default=4,
                    help="Parallel solver workers (default: %(default)s)")
    ap.add_argument("--max-instances", type=int, default=0,
                    help="Stop after N candidates (0 = no limit)")
    ap.add_argument("--index", default=str(DEFAULT_INDEX),
                    help="Path to curated.jsonl (default: %(default)s)")
    ap.add_argument("--refresh", action="store_true",
                    help="Re-run on instances already in the index "
                         "(overrides previous entry)")
    ap.add_argument("--include-sat-assignments", action="store_true",
                    help="Keep full assignment in the index (large for big "
                         "instances). Default: only the verification bit.")
    # --verify-unsat: chain into verify_unsat.verify_one after each UNSAT
    # verdict so the record carries drat_verified + stats in one pass.
    ap.add_argument("--verify-unsat", action="store_true",
                    help="On each UNSAT result, immediately generate a DRAT "
                         "proof with standalone `cadical` and verify with "
                         "`drat-trim` (writes drat_verified into the record). "
                         "Same effect as running tools/gbd/verify_unsat.py "
                         "afterwards.")
    ap.add_argument("--verify-timeout", type=int, default=60,
                    help="Per-instance DRAT emission + verification budget "
                         "(default: %(default)s)")
    ap.add_argument("--cadical-bin", default=shutil.which("cadical"),
                    help="Standalone cadical (default: auto-detect from PATH); "
                         "only used with --verify-unsat")
    ap.add_argument("--drat-trim-bin", default=str(DEFAULT_DRAT_TRIM),
                    help="drat-trim binary path (default: %(default)s); "
                         "only used with --verify-unsat")
    ap.add_argument("--keep-proofs", action="store_true",
                    help="With --verify-unsat: retain .drat files in "
                         "--proofs-dir (default: delete after verification)")
    ap.add_argument("--proofs-dir", default=str(BENCH_DIR / "drat_proofs"),
                    help="Where --keep-proofs writes .drat files")
    args = ap.parse_args()

    # If --verify-unsat is on, build the drat_cfg dict that solve_one
    # will pass to verify_one.  Validate the tools exist up front.
    drat_cfg = None
    if args.verify_unsat:
        if not args.cadical_bin or not Path(args.cadical_bin).exists():
            print("FATAL: --verify-unsat needs cadical; brew install cadical "
                  "or pass --cadical-bin PATH", file=sys.stderr)
            sys.exit(2)
        if not Path(args.drat_trim_bin).exists():
            print(f"FATAL: --verify-unsat needs drat-trim at "
                  f"{args.drat_trim_bin}", file=sys.stderr)
            print("  build with: git clone "
                  "https://github.com/marijnheule/drat-trim.git "
                  "~/projects/drat-trim && cd ~/projects/drat-trim && make",
                  file=sys.stderr)
            sys.exit(2)
        drat_cfg = {
            "timeout": args.verify_timeout,
            "cadical": args.cadical_bin,
            "drat_trim": args.drat_trim_bin,
            "proofs_dir": args.proofs_dir if args.keep_proofs else None,
            "keep_proofs": args.keep_proofs,
        }

    if not SAT_BIN.exists():
        print(f"FATAL: sat binary not found at {SAT_BIN}", file=sys.stderr)
        print("  build with: cargo build --release --bin sat", file=sys.stderr)
        sys.exit(2)

    index_path = Path(args.index)
    index = load_index(index_path)
    print(f"loaded index: {len(index)} prior entries from {index_path}")

    # Resolve hashes via GBD.
    print(f"querying GBD: {args.query!r}")
    candidates = gbd_query(args.query)
    print(f"candidates:   {len(candidates)}")

    # Filter: only ones we have locally, and (unless --refresh) skip
    # ones already in the index.
    queue = []
    missing = 0
    in_index = 0
    for hash_, fname in candidates:
        xz = find_cnf(hash_)
        if not xz:
            missing += 1
            continue
        if not args.refresh and hash_ in index:
            in_index += 1
            continue
        queue.append((hash_, fname, xz, args.timeout, drat_cfg))
        if args.max_instances and len(queue) >= args.max_instances:
            break
    print(f"missing on disk:     {missing}  (run tools/gbd/download.sh to fetch)")
    print(f"already in index:    {in_index}  (use --refresh to re-solve)")
    print(f"to solve:            {len(queue)}")
    if not queue:
        return

    print(f"running cadical with {args.timeout}s budget, parallel={args.parallel}...")

    # Open the index file for appending.
    with open(index_path, "a") as fout, ProcessPoolExecutor(max_workers=args.parallel) as ex:
        futures = {ex.submit(solve_one, item): item for item in queue}
        n_sat = n_unsat = n_to = n_err = 0
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

            # Trim assignment unless caller asked to keep it.
            if not args.include_sat_assignments and "assignment" in rec:
                rec.pop("assignment", None)

            fout.write(json.dumps(rec) + "\n")
            fout.flush()
            elapsed = rec.get("time_ms")
            tag = f"{elapsed:7.1f}ms" if elapsed is not None else "      -"
            # Add DRAT outcome if chained verification was done.
            drat_tag = ""
            if "drat_verified" in rec:
                dv = rec["drat_verified"]
                if dv is True:
                    drat_tag = "  DRAT✓"
                elif dv is False:
                    drat_tag = "  DRAT✗"
                else:
                    drat_tag = "  DRAT?"
            print(f"[{i:4}/{len(queue)}] {status:7}  {tag}{drat_tag}  {item[1]}")

    print()
    print("=== summary ===")
    print(f"  SAT:     {n_sat}")
    print(f"  UNSAT:   {n_unsat}")
    print(f"  TIMEOUT: {n_to}")
    print(f"  ERROR:   {n_err}")
    print(f"index file: {index_path}")


if __name__ == "__main__":
    main()
