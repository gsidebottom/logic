#!/usr/bin/env python3
"""Which stage-decided instances satsuma decides anyway: satsuma's symmetry
step alone (fix mode, the competition flags, no kissat) on every instance a
hydra stage decides in a duo run's stage scan, then a report that classes
each instance by what the step does and, for those satsuma has reached,
what satsuma's result was.  A unique win for hydra_circuit_satsuma needs a
stage-decided instance satsuma fails, and in reuse mode nothing else can be
one, so the classes predict the run's unique wins before satsuma gets there.

    tools/gbd/sym_probe.py                  # probe what is missing, then report
    tools/gbd/sym_probe.py --report-only

Classes: "refuted" (the step alone derives the empty clause), "breaks"
(it adds units, binaries or lex clauses but does not refute), "none"
(dejavu finds no symmetry).  One container at a time, 120 s cap each, beside
the duo run.  Probe results: RUN/sym_probe.jsonl (resumable).
"""
import argparse
import collections
import csv
import json
import re
import shutil
import subprocess
import time
from pathlib import Path

B = Path("/Users/greg/projects/sat_benchmarks")
KEYS = ("dejavu_gens", "row", "row_column", "johnson", "symmetry_units", "orbitopal_units",
        "symmetry_binary", "amo_binary", "symmetry_lex", "iterations", "propagations")
FIX = ("cd /src && timeout 120s ./satsuma fix /work/f.cnf --full-skip-limit 100000000 "
       "--add-reduced-as-unit --bsr --proof-file /work/proof.out --out-file /work/sb.cnf; echo rc=$?")


def probe_one(h, work):
    rec = dict(hash=h)
    xz = next(iter(sorted(B.glob(f"{h}-*.cnf.xz"))), None)
    if xz is None:
        rec["error"] = "missing"
        return rec
    # A fresh directory per instance: Docker Desktop's file sharing can serve
    # a stale view of a file deleted and recreated under the same name.
    w = work / h
    shutil.rmtree(w, ignore_errors=True)
    w.mkdir(parents=True)
    with open(w / "f.cnf", "wb") as f:
        subprocess.run(["xz", "-dc", str(xz)], stdout=f, check=True)
    t0 = time.time()
    try:
        p = subprocess.run(["docker", "run", "--rm", "-v", f"{w}:/work", "satsuma-iter-kissat", "bash", "-c", FIX],
                           capture_output=True, text=True, timeout=200)
        txt = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        txt = "rc=timeout"
    rec["wall_s"] = round(time.time() - t0, 2)
    m = re.search(r"rc=(\S+)", txt)
    rec["rc"] = m.group(1) if m else None
    for k in KEYS:
        m = re.search(rf"c {k}\s+=\s+(\d+)", txt)
        if m:
            rec[k] = int(m.group(1))
    m = re.search(r"c\s+([0-9.]+)ms\s+100% total", txt)
    rec["satsuma_ms"] = float(m.group(1)) if m else None
    sb = w / "sb.cnf"
    if sb.exists():
        n = units = 0
        empty = False
        for line in open(sb):
            if line[:1] in "cp" or not line.strip():
                continue
            n += 1
            t = line.split()
            if t == ["0"]:
                empty = True
            elif len(t) == 2:
                units += 1
        rec.update(out_clauses=n, out_units=units, empty=empty)
    shutil.rmtree(w, ignore_errors=True)
    return rec


def klass(p):
    if not p or "dejavu_gens" not in p:
        return "no probe"
    if p.get("empty"):
        return "refuted"
    if p["dejavu_gens"] == 0:
        return "none"
    if sum(p.get(k, 0) for k in ("symmetry_units", "symmetry_binary", "symmetry_lex", "row", "row_column", "johnson")):
        return "breaks"
    return "found, nothing added"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--run", default=str(B / "runs" / "anni_2022_duo"))
    ap.add_argument("--reference", default=str(B / "sc2022" / "anni-seq.csv"))
    ap.add_argument("--source", default="satsuma", help="the backend whose failures make unique wins")
    ap.add_argument("--report-only", action="store_true")
    args = ap.parse_args()
    run = Path(args.run)
    out = run / "sym_probe.jsonl"
    scan = {}
    for line in open(run / "stage_scan.jsonl"):
        s = json.loads(line)
        if s.get("outcome", "").startswith("decided"):
            scan[s["hash"]] = s
    probe = {}
    if out.exists():
        for line in open(out):
            p = json.loads(line)
            probe[p["hash"]] = p
    if not args.report_only:
        work = Path("/tmp/sym_probe")
        with open(out, "a") as f:
            for h in scan:
                if h not in probe:
                    probe[h] = probe_one(h, work)
                    f.write(json.dumps(probe[h]) + "\n")
                    f.flush()

    cfg = json.load(open(run / "config.json"))
    pos = {h: i + 1 for i, h in enumerate(cfg["order"])}
    res = {}
    for line in open(run / "results.jsonl"):
        try:
            r = json.loads(line)
            res[(r["hash"], r["backend"])] = r
        except (ValueError, KeyError):
            pass
    ref = {r["hash"]: r for r in csv.DictReader(open(args.reference))} if Path(args.reference).exists() else {}
    sv = [k for k in next(iter(ref.values()), {}) if k not in ("hash", "benchmark", "verified-result", "claimed-result")]

    def field(h):
        if h not in ref:
            return ""
        t = sorted(float(ref[h][s]) for s in sv)
        ok = [x for x in t if x < 5000]
        return f"2022 {len(ok)}/{len(t)}" + (f", best {ok[0]:.0f} s" if ok else "")

    def unsolved22(h):
        return h in ref and all(float(ref[h][s]) >= 5000 for s in sv)

    rows = sorted(scan, key=lambda h: pos.get(h, 10**9))
    print(f"{len(rows)} stage-decided instances; satsuma's symmetry step alone:")
    for k, n in collections.Counter(klass(probe.get(h)) for h in rows).most_common():
        print(f"  {k:22s} {n:4d}")
    print(f"\nreached by {args.source}, its result by class:")
    for k in ("refuted", "breaks", "none", "found, nothing added", "no probe"):
        hs = [h for h in rows if klass(probe.get(h)) == k and (h, args.source) in res]
        if not hs:
            continue
        ok = sorted(res[(h, args.source)]["time_s"] for h in hs if res[(h, args.source)]["result"] in ("SAT", "UNSAT"))
        print(f"  {k:22s} reached {len(hs):4d}, solved {len(ok):4d}" +
              (f", median {ok[len(ok) // 2]:.2f} s, max {ok[-1]:.1f} s" if ok else ""))
        for h in hs:
            r = res[(h, args.source)]
            if r["result"] not in ("SAT", "UNSAT"):
                print(f"      failed #{pos[h]:<5} {r['name'][:44]:44s} {field(h)}")
    print(f"\nnot yet reached, symmetry step does not refute (the possible unique wins):")
    for h in rows:
        p = probe.get(h)
        if (h, args.source) in res or klass(p) == "refuted":
            continue
        rec = cfg["records"][h]
        print(f"  #{pos[h]:<5} {rec['name'][:42]:42s} {scan[h]['outcome'].split()[-1]:9s} "
              f"{rec['nvars']:6d} v {rec['nclauses']:7d} cl  {klass(p):7s} gens {p.get('dejavu_gens', '?'):>4} "
              f"units {p.get('symmetry_units', 0):>4} bin {p.get('symmetry_binary', 0):>3}  {field(h)}")
    left = [h for h in rows if (h, args.source) not in res and klass(probe.get(h)) == "refuted"]
    print(f"\nnot yet reached, refuted by the symmetry step: {len(left)}, "
          f"{sum(unsolved22(h) for h in left)} of them unsolved by all of 2022")


if __name__ == "__main__":
    main()
