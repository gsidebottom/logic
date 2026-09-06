#!/usr/bin/env python3
"""M1 gate for the box-matrix backend: run `sat -b boxes` on the curated corpus
and compare each verdict with the index's known status (SAT verdicts there are
witness-verified, UNSAT ones certified).  Reports agreement, disagreement,
timeouts, and per-instance time.

Usage: tools/boxes_verdict_check.py [--max-clauses N] [--timeout S] [--sat BIN] [--limit K]
"""
import argparse, json, lzma, os, subprocess, sys, time

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--index", default="evo/curated_struct_eff.jsonl")
    ap.add_argument("--max-clauses", type=int, default=1000)
    ap.add_argument("--timeout", type=int, default=30)
    ap.add_argument("--sat", default="target/release/sat")
    ap.add_argument("--backend", default="boxes")
    ap.add_argument("--limit", type=int, default=0)
    a = ap.parse_args()
    rows = [json.loads(l) for l in open(a.index) if l.strip()]
    rows = [r for r in rows if r.get("status") in ("SAT", "UNSAT") and r.get("nclauses", 1 << 30) <= a.max_clauses]
    rows.sort(key=lambda r: r["nclauses"])
    if a.limit: rows = rows[:a.limit]
    agree = disagree = timeout = other = 0
    for r in rows:
        path = os.path.join(os.path.dirname(a.index), r["xz_path"])
        cnf = lzma.open(path).read()
        t0 = time.time()
        try:
            p = subprocess.run([a.sat, "-b", a.backend, "--timeout", str(a.timeout), "--no-preprocess"],
                               input=cnf, capture_output=True, timeout=a.timeout + 15)
            out = p.stdout.decode(errors="replace")
        except subprocess.TimeoutExpired:
            out = ""
        dt = time.time() - t0
        verdict = "SAT" if "s SATISFIABLE" in out else "UNSAT" if "s UNSATISFIABLE" in out else ("TIMEOUT" if dt >= a.timeout else "NONE")
        stats = next((l for l in p.stderr.decode(errors="replace").splitlines() if l.startswith("c boxes:")), "") if out else ""
        if verdict == r["status"]: agree += 1; tag = "ok  "
        elif verdict in ("SAT", "UNSAT"): disagree += 1; tag = "MISMATCH"
        elif verdict == "TIMEOUT": timeout += 1; tag = "timeout"
        else: other += 1; tag = "none"
        print(f"{tag:8} {r['filename'][:44]:44} n={r['nvars']:6} m={r['nclauses']:6} expect={r['status']:5} got={verdict:7} {dt:6.2f}s  {stats}")
        sys.stdout.flush()
    print(f"\nagree={agree} disagree={disagree} timeout={timeout} other={other} of {len(rows)}")
    sys.exit(1 if disagree else 0)

if __name__ == "__main__":
    main()
