#!/usr/bin/env python3
"""
DRAT-cross-check UNSAT verdicts in a curated index.

For each record in the index with `status == "UNSAT"`:
  1. Decompress the .cnf (kept; .cnf deleted after).
  2. Run `cadical <cnf> <proof.drat> --no-binary` to generate a DRAT
     proof of unsatisfiability.
  3. Run `drat-trim <cnf> <proof.drat>` to independently verify.
  4. Update the record with `drat_verified: true | false | "error"`
     plus the time spent on emission + verification.
  5. (Optionally) keep the DRAT file for audit; default deletes it.

The index file is rewritten in place (atomic via temp + rename).

Re-runnable: by default, skips records already marked
`drat_verified=true`.  Use `--refresh` to re-verify everything.

Dependencies:
  - `cadical` on $PATH (brew install cadical)
  - drat-trim at ~/projects/drat-trim/drat-trim  (or pass --drat-trim PATH)

Usage:
    verify_unsat.py [--index PATH] [--timeout SECS] [--parallel N]
                    [--keep-proofs] [--refresh] [--drat-trim PATH]

Examples:
    # Verify default index, 60s budget per instance:
    tools/gbd/verify_unsat.py --timeout 60

    # Re-verify everything from scratch:
    tools/gbd/verify_unsat.py --refresh

    # Keep .drat files in a chosen directory:
    tools/gbd/verify_unsat.py --keep-proofs --proofs-dir /tmp/drat
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
BENCH_DIR = Path(os.environ.get("BENCH_DIR", "/Users/greg/projects/sat_benchmarks"))
DEFAULT_INDEX = BENCH_DIR / "curated.jsonl"
DEFAULT_DRAT_TRIM = Path.home() / "projects" / "drat-trim" / "drat-trim"


def load_index(path):
    """Read the JSONL index into a list of (line, parsed_obj) tuples
    preserving order so we can rewrite the file with updates."""
    records = []
    if not path.exists():
        return records
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if not line:
                continue
            try:
                obj = json.loads(line)
                records.append(obj)
            except Exception as e:
                print(f"WARN: skipping malformed line ({e}): {line[:80]}",
                      file=sys.stderr)
    return records


def write_index(path, records):
    """Atomic rewrite: write to tmp + rename."""
    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, "w") as f:
        for r in records:
            f.write(json.dumps(r) + "\n")
    tmp.replace(path)


def verify_one(args):
    """Per-instance worker.

    Returns a (hash, update_dict) pair.  update_dict has the keys to
    merge into the record:
       - drat_verified: True | False | "error"
       - drat_cadical_ms, drat_trim_ms: timings
       - drat_lemmas, drat_resolutions: stats from drat-trim
       - drat_error: error string on failure
    """
    hash_ = args["hash"]
    xz_path = Path(args["xz_path"])
    timeout_s = args["timeout"]
    cadical_bin = args["cadical"]
    drat_trim_bin = args["drat_trim"]
    proofs_dir = Path(args["proofs_dir"]) if args["proofs_dir"] else None
    keep_proofs = args["keep_proofs"]

    cnf_path = Path(str(xz_path)[:-3])  # strip .xz
    cleanup_cnf = False
    if not cnf_path.exists():
        try:
            subprocess.run(["xz", "-d", "-k", str(xz_path)], check=True,
                           capture_output=True)
            cleanup_cnf = True
        except subprocess.CalledProcessError as e:
            return hash_, {"drat_verified": "error",
                           "drat_error": f"xz decompress: {e.stderr.decode()[:200]}"}

    # Pick a proof file path.
    if proofs_dir and keep_proofs:
        proofs_dir.mkdir(parents=True, exist_ok=True)
        proof_path = proofs_dir / f"{hash_}.drat"
    else:
        proof_path = Path(str(cnf_path) + ".drat.tmp")

    update = {}

    # Step 1: cadical generates DRAT.
    t0 = time.time()
    try:
        # cadical exits 20 on UNSAT (proof produced), 10 on SAT, 0 on
        # other.  Any of {0, 10, 20} is "ran successfully"; SAT (10) is
        # unexpected since the record is supposedly UNSAT.
        proc = subprocess.run(
            [cadical_bin, str(cnf_path), str(proof_path), "--no-binary",
             "-t", str(timeout_s)],
            capture_output=True, text=True, timeout=timeout_s + 10,
        )
    except subprocess.TimeoutExpired:
        update["drat_verified"] = "error"
        update["drat_error"] = f"cadical wall-timeout after {timeout_s}s"
        if not keep_proofs:
            proof_path.unlink(missing_ok=True)
        if cleanup_cnf:
            cnf_path.unlink(missing_ok=True)
        return hash_, update
    update["drat_cadical_ms"] = (time.time() - t0) * 1000.0

    # Detect outcome.  cadical exit code 20 = UNSAT (proof valid),
    # 10 = SAT (record was wrong about UNSAT!), other = error.
    if proc.returncode == 10:
        update["drat_verified"] = False
        update["drat_error"] = ("cadical reports SAT; the index's UNSAT "
                                "verdict was wrong")
        if not keep_proofs:
            proof_path.unlink(missing_ok=True)
        if cleanup_cnf:
            cnf_path.unlink(missing_ok=True)
        return hash_, update
    if proc.returncode != 20:
        update["drat_verified"] = "error"
        update["drat_error"] = (f"cadical exit {proc.returncode}: "
                                f"{(proc.stderr or proc.stdout)[-200:]}")
        if not keep_proofs:
            proof_path.unlink(missing_ok=True)
        if cleanup_cnf:
            cnf_path.unlink(missing_ok=True)
        return hash_, update

    if not proof_path.exists() or proof_path.stat().st_size == 0:
        update["drat_verified"] = "error"
        update["drat_error"] = "cadical exited UNSAT but proof file is empty"
        if cleanup_cnf:
            cnf_path.unlink(missing_ok=True)
        return hash_, update

    update["drat_proof_bytes"] = proof_path.stat().st_size

    # Step 2: drat-trim verifies.
    t0 = time.time()
    try:
        proc = subprocess.run(
            [drat_trim_bin, str(cnf_path), str(proof_path)],
            capture_output=True, text=True, timeout=timeout_s * 2 + 30,
        )
    except subprocess.TimeoutExpired:
        update["drat_verified"] = "error"
        update["drat_error"] = "drat-trim wall-timeout"
        if not keep_proofs:
            proof_path.unlink(missing_ok=True)
        if cleanup_cnf:
            cnf_path.unlink(missing_ok=True)
        return hash_, update
    update["drat_trim_ms"] = (time.time() - t0) * 1000.0

    out = proc.stdout + proc.stderr
    # drat-trim prints "s VERIFIED" on success, "s NOT VERIFIED" on failure.
    if "s VERIFIED" in out:
        update["drat_verified"] = True
        # Extract stats: "c 22 of 22 clauses in core" / "c X of Y lemmas in core"
        for line in out.splitlines():
            if "lemmas in core" in line:
                # "c 44 of 49 lemmas in core using 89 resolution steps"
                tok = line.split()
                try:
                    update["drat_lemmas"] = int(tok[1])
                    update["drat_resolutions"] = int(tok[7])
                except (ValueError, IndexError):
                    pass
    elif "s NOT VERIFIED" in out:
        update["drat_verified"] = False
        update["drat_error"] = "drat-trim reports NOT VERIFIED"
    else:
        update["drat_verified"] = "error"
        update["drat_error"] = f"drat-trim unclear: {out[-300:]}"

    if not keep_proofs:
        proof_path.unlink(missing_ok=True)
    if cleanup_cnf:
        cnf_path.unlink(missing_ok=True)
    return hash_, update


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--index", default=str(DEFAULT_INDEX),
                    help="Path to curated.jsonl (default: %(default)s)")
    ap.add_argument("--timeout", type=int, default=60,
                    help="Per-instance budget for cadical + drat-trim "
                         "(default: %(default)s)")
    ap.add_argument("--parallel", type=int, default=4,
                    help="Parallel workers (default: %(default)s)")
    ap.add_argument("--refresh", action="store_true",
                    help="Re-verify records already marked drat_verified=true")
    ap.add_argument("--keep-proofs", action="store_true",
                    help="Don't delete .drat files; save them in --proofs-dir")
    ap.add_argument("--proofs-dir", default=str(BENCH_DIR / "drat_proofs"),
                    help="Where to save .drat files when --keep-proofs is on "
                         "(default: %(default)s)")
    ap.add_argument("--cadical", default=shutil.which("cadical"),
                    help="cadical binary (default: auto-detect from PATH)")
    ap.add_argument("--drat-trim", default=str(DEFAULT_DRAT_TRIM),
                    help="drat-trim binary (default: %(default)s)")
    args = ap.parse_args()

    if not args.cadical or not Path(args.cadical).exists():
        print("FATAL: cadical not found; brew install cadical", file=sys.stderr)
        sys.exit(2)
    if not Path(args.drat_trim).exists():
        print(f"FATAL: drat-trim not found at {args.drat_trim}", file=sys.stderr)
        print("  build with: git clone https://github.com/marijnheule/drat-trim "
              "~/projects/drat-trim && cd ~/projects/drat-trim && make",
              file=sys.stderr)
        sys.exit(2)

    index_path = Path(args.index)
    records = load_index(index_path)
    if not records:
        print(f"index empty: {index_path}", file=sys.stderr)
        return

    # Build the worklist: UNSAT records that need verification.
    queue = []
    for rec in records:
        if rec.get("status") != "UNSAT":
            continue
        if not args.refresh and rec.get("drat_verified") is True:
            continue
        queue.append({
            "hash": rec["hash"],
            "xz_path": rec["xz_path"],
            "timeout": args.timeout,
            "cadical": args.cadical,
            "drat_trim": args.drat_trim,
            "proofs_dir": args.proofs_dir if args.keep_proofs else None,
            "keep_proofs": args.keep_proofs,
        })

    n_unsat = sum(1 for r in records if r.get("status") == "UNSAT")
    n_already = n_unsat - len(queue)
    print(f"index has {len(records)} records, {n_unsat} UNSAT")
    print(f"  already verified: {n_already}")
    print(f"  to verify:        {len(queue)}")
    if not queue:
        return

    # Process in parallel, then merge updates back into records.
    updates = {}  # hash -> update dict
    print(f"running cadical+drat-trim with {args.timeout}s budget, "
          f"parallel={args.parallel}...")
    with ProcessPoolExecutor(max_workers=args.parallel) as ex:
        futures = {ex.submit(verify_one, item): item for item in queue}
        n_ok = n_wrong = n_err = 0
        for i, fut in enumerate(as_completed(futures), 1):
            item = futures[fut]
            try:
                hash_, upd = fut.result()
            except Exception as e:
                hash_ = item["hash"]
                upd = {"drat_verified": "error",
                       "drat_error": f"worker exception: {e}"}
            updates[hash_] = upd
            v = upd.get("drat_verified")
            if v is True:
                n_ok += 1
                tag = "VERIFIED"
            elif v is False:
                n_wrong += 1
                tag = "WRONG-UNSAT"
            else:
                n_err += 1
                tag = "ERROR"
            ms_c = upd.get("drat_cadical_ms")
            ms_t = upd.get("drat_trim_ms")
            ms_str = (f"cadical={ms_c:.0f}ms drat-trim={ms_t:.0f}ms"
                      if ms_c and ms_t else "-")
            # Find filename for display.
            fn = next((r["filename"] for r in records if r["hash"] == hash_), hash_)
            print(f"[{i:4}/{len(queue)}] {tag:11}  {ms_str:35}  {fn}")

    # Merge updates into records and rewrite the index.
    for rec in records:
        if rec["hash"] in updates:
            rec.update(updates[rec["hash"]])
    write_index(index_path, records)

    print()
    print("=== summary ===")
    print(f"  VERIFIED:    {n_ok}")
    print(f"  WRONG-UNSAT: {n_wrong}  ← these are soundness bugs in the source!")
    print(f"  ERROR:       {n_err}")
    print(f"index file: {index_path}")
    if args.keep_proofs:
        print(f"proofs kept in: {args.proofs_dir}")


if __name__ == "__main__":
    main()
