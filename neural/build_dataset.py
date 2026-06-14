#!/usr/bin/env python3
"""
Phase 0b — build the supervised phase-prediction dataset.

For each instance in an index: solve it; if SATISFIABLE, take the model and
record each variable's **phase** (its value in the satisfying assignment) —
the NeuroBack target.  Pair the labels with the literal–clause graph
(sat_graph.py) and save one compressed .npz per SAT instance, plus a
manifest covering every instance (incl. UNSAT/timeout, for later
SAT/UNSAT-classification use) and a family-stratified train/test split.

  MVP labels = a SINGLE satisfying assignment's phases.  NeuroBack's
  "majority over many models" is a documented refinement (sample k models
  via blocking clauses, majority-vote per var) — left for Phase 0b+.

Each saved .npz holds: edge_lit, edge_clause, flip (int32), n_vars,
n_clauses (int), phase (uint8[n_vars]).  Labels are re-verified against the
CNF before saving (a bad model can then only shrink the dataset, never
poison it).

Usage:
  build_dataset.py --index <jsonl> --out <dir> [-t SECS] [-j N]
                   [--limit N] [--max-vars N] [--max-clauses N] [--no-verify]
Index records: {filename, family, (xz_path | path), nvars?, nclauses?}.
"""
from __future__ import annotations

import argparse
import json
import lzma
import os
import subprocess
import sys
import tempfile
import hashlib
from concurrent.futures import ThreadPoolExecutor

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sat_graph  # noqa: E402


def find_solver() -> str:
    for p in ("/opt/homebrew/bin/cadical", "/usr/local/bin/cadical",
              "/usr/bin/cadical"):
        if os.path.exists(p):
            return p
    return "cadical"


SOLVER = find_solver()


def _cnf_path_for_solver(rec: dict, tmpdir: str) -> str:
    """Return a plain DIMACS path the solver can read, decompressing .xz."""
    src = rec.get("xz_path") or rec["path"]
    if src.endswith(".xz"):
        dst = os.path.join(tmpdir, "inst.cnf")
        with lzma.open(src, "rb") as fi, open(dst, "wb") as fo:
            fo.write(fi.read())
        return dst
    return src


def solve_model(cnf_path: str, timeout: int):
    """Run the solver. Returns (verdict, model) where verdict is
    'SAT'|'UNSAT'|'UNKNOWN' and model maps var -> bool (only for SAT)."""
    cmd = [SOLVER, "-q"]
    if timeout > 0:
        cmd += ["-t", str(timeout)]
    cmd += [cnf_path]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True,
                           timeout=timeout + 30 if timeout else None)
    except subprocess.TimeoutExpired:
        return "UNKNOWN", None
    out = p.stdout
    if "s SATISFIABLE" in out:
        model: dict[int, bool] = {}
        for line in out.splitlines():
            if line.startswith("v "):
                for tok in line[2:].split():
                    lit = int(tok)
                    if lit != 0:
                        model[abs(lit)] = lit > 0
        return "SAT", model
    if "s UNSATISFIABLE" in out:
        return "UNSAT", None
    return "UNKNOWN", None


def model_satisfies(clauses, model: dict[int, bool]) -> bool:
    for c in clauses:
        if not any(model.get(abs(l), False) == (l > 0) for l in c):
            return False
    return True


def process(rec: dict, out_dir: str, timeout: int, verify: bool) -> dict:
    """Solve one instance; on SAT, save its graph + phase labels. Returns a
    manifest entry."""
    name = rec.get("filename", rec.get("path", "?"))
    h = hashlib.sha1(name.encode()).hexdigest()[:16]
    entry = {"hash": h, "filename": name, "family": rec.get("family"),
             "verdict": None, "n_vars": None, "n_clauses": None,
             "sat": None, "saved": False, "split": None}
    with tempfile.TemporaryDirectory() as td:
        try:
            cnf = _cnf_path_for_solver(rec, td)
        except Exception as e:
            entry["verdict"] = f"ERR:{type(e).__name__}"
            return entry
        verdict, model = solve_model(cnf, timeout)
        entry["verdict"] = verdict
        if verdict not in ("SAT", "UNSAT"):
            return entry                          # UNKNOWN/timeout → no graph
        nvars, clauses = sat_graph.parse_dimacs(cnf)
        entry["n_vars"], entry["n_clauses"] = nvars, len(clauses)
        sat = 1 if verdict == "SAT" else 0
        phase = np.zeros(nvars, dtype=np.uint8)   # meaningful only when sat==1
        if sat:
            # complete the model (solver may omit don't-care vars → False)
            full = {v: model.get(v, False) for v in range(1, nvars + 1)}
            if verify and not model_satisfies(clauses, full):
                entry["verdict"] = "SAT-BADMODEL"  # dropped from dataset
                return entry
            phase = np.fromiter((1 if full[v] else 0 for v in range(1, nvars + 1)),
                                dtype=np.uint8, count=nvars)
        g = sat_graph.build_graph(clauses, nvars)
        np.savez_compressed(
            os.path.join(out_dir, f"{h}.npz"),
            edge_lit=g.edge_lit, edge_clause=g.edge_clause, flip=g.flip,
            n_vars=np.int64(nvars), n_clauses=np.int64(len(clauses)),
            sat=np.int8(sat), phase=phase)
        entry["sat"] = sat
        entry["saved"] = True
    return entry


def assign_splits(entries: list[dict], test_frac: float) -> None:
    """Family-stratified, deterministic train/test split over labeled rows."""
    from collections import defaultdict
    by_grp: dict = defaultdict(list)
    for e in entries:
        if e["saved"]:
            by_grp[(e["family"] or "?", e["sat"])].append(e)   # balance classes
    for grp, rows in by_grp.items():
        rows.sort(key=lambda e: e["hash"])      # deterministic
        n_test = max(1, round(len(rows) * test_frac)) if len(rows) > 1 else 0
        for i, e in enumerate(rows):
            e["split"] = "test" if i < n_test else "train"


def read_index(path: str):
    if path.endswith(".jsonl"):
        return [json.loads(l) for l in open(path) if l.strip()]
    return [json.loads(open(path).read())]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--index", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("-t", "--timeout", type=int, default=60)
    ap.add_argument("-j", "--jobs", type=int, default=4)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--max-vars", type=int, default=200_000)
    ap.add_argument("--max-clauses", type=int, default=2_000_000)
    ap.add_argument("--test-frac", type=float, default=0.2)
    ap.add_argument("--no-verify", action="store_true")
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    recs = read_index(args.index)
    # size filter (keep Phase-0 instances trainable; giants skipped)
    kept = [r for r in recs
            if (r.get("nvars") or 0) <= args.max_vars
            and (r.get("nclauses") or 0) <= args.max_clauses]
    if args.limit:
        kept = kept[:args.limit]
    print(f"index {args.index}: {len(recs)} records, {len(kept)} within size "
          f"caps ({args.max_vars} vars / {args.max_clauses} clauses)")

    entries: list[dict] = []
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = [ex.submit(process, r, args.out, args.timeout, not args.no_verify)
                for r in kept]
        for i, f in enumerate(futs, 1):
            e = f.result()
            entries.append(e)
            if i % 25 == 0 or i == len(futs):
                sv = sum(1 for x in entries if x["saved"])
                print(f"  {i}/{len(futs)} solved  ({sv} graphs saved)")

    assign_splits(entries, args.test_frac)
    with open(os.path.join(args.out, "manifest.jsonl"), "w") as f:
        for e in entries:
            f.write(json.dumps(e) + "\n")

    from collections import Counter
    verd = Counter(e["verdict"] for e in entries)
    saved = [e for e in entries if e["saved"]]
    n_sat = sum(1 for e in saved if e["sat"]); n_uns = len(saved) - n_sat
    spl = Counter((e["split"], "SAT" if e["sat"] else "UNSAT") for e in saved)
    print(f"\ndataset → {args.out}")
    print(f"  verdicts: {dict(verd)}")
    print(f"  saved graphs: {len(saved)}  (SAT={n_sat} UNSAT={n_uns})")
    print(f"  split: train[SAT={spl.get(('train','SAT'),0)} "
          f"UNSAT={spl.get(('train','UNSAT'),0)}]  "
          f"test[SAT={spl.get(('test','SAT'),0)} "
          f"UNSAT={spl.get(('test','UNSAT'),0)}]")
    if saved:
        vs = sorted(e["n_vars"] for e in saved)
        print(f"  var counts: min={vs[0]} median={vs[len(vs)//2]} max={vs[-1]}")


if __name__ == "__main__":
    main()
