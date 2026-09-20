#!/usr/bin/env python3
"""Build a family-balanced study set for engine A/Bs, from local files only.

Why this exists alongside `curate_balanced.py`: that tool queries GBD's
databases over the network and, within each family, takes the *smallest*
instances because it is curating a fast fitness loop.  Both choices are
wrong for measuring search quality.  Smallest-first reproduces the bias it
is meant to fix — you end up tuning on instances that finish in under a
second — and the network is not always there.

This selects from the competition index already on disk, and ranks within
a family by *recorded solve time* from a previous portfolio run rather
than by size, keeping instances in a difficulty band.  It caps per-family
contribution the same way.

The bias it fixes, measured 2026-09-20: the A/B corpus the engine's
chrono / shrink / restart / reduce verdicts were taken on is 22 classic
instances covering ~10 families, 14 of them from just two (ISCAS circuits
and random 3-SAT), with a median solve time of 0.91 s against the
competition's 85.5 s.  Neutral on that sample is not neutral.

Usage:
    tools/gbd/study_set.py --per-family 2 --band 1,300 \\
        --out /tmp/study/manifest.jsonl --extract /tmp/study/cnf
"""
import argparse
import collections
import json
import lzma
import os
import pathlib
import sys

DEFAULT_INDEX = "/Users/greg/projects/sat_benchmarks/main_track_2026_official.jsonl"
DEFAULT_RESULTS = "doc/competition-benchmark_main_track_2026_official_5000_satsuma.json"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--index", default=DEFAULT_INDEX,
                    help="JSONL of {hash, family, xz_path, status}")
    ap.add_argument("--results", default=DEFAULT_RESULTS,
                    help="a previous run's JSON, for per-instance solve times")
    ap.add_argument("--per-family", type=int, default=2,
                    help="hard cap on instances taken from any one family")
    ap.add_argument("--band", default="1,300",
                    help="keep instances whose recorded solve time is in LOW,HIGH seconds")
    ap.add_argument("--out", required=True, help="manifest JSONL to write")
    ap.add_argument("--extract", default=None,
                    help="decompress the selected .cnf.xz into this directory")
    a = ap.parse_args()

    lo, hi = (float(x) for x in a.band.split(","))
    idx = [json.loads(l) for l in open(a.index)]
    run = json.load(open(a.results))["results"]
    rec = {r["hash"]: (r["result"], r.get("time_s")) for r in run}

    # Candidates: a known verdict (so an A/B can check answers, not just
    # times) and a recorded time inside the band (so they are neither
    # trivial nor hopeless).
    cand = []
    for r in idx:
        v, t = rec.get(r["hash"], (None, None))
        if v in ("SAT", "UNSAT") and t and lo <= t <= hi and os.path.isfile(r["xz_path"]):
            cand.append(dict(r, verdict=v, portfolio_s=t))

    # Within a family take the SLOWEST first: the whole point is to stop
    # measuring on instances that finish before the solver warms up.  Then
    # alternate SAT and UNSAT so neither dominates a family's slots.
    byfam = collections.defaultdict(list)
    for c in cand:
        byfam[c["family"]].append(c)
    picked = []
    for fam, cs in sorted(byfam.items()):
        cs.sort(key=lambda c: -c["portfolio_s"])
        sat = [c for c in cs if c["verdict"] == "SAT"]
        uns = [c for c in cs if c["verdict"] == "UNSAT"]
        take, i = [], 0
        while len(take) < a.per_family and (sat or uns):
            src = (sat if (i % 2 == 0 and sat) else uns) or sat
            take.append(src.pop(0))
            i += 1
        picked.extend(take)

    picked.sort(key=lambda c: (c["family"], -c["portfolio_s"]))
    pathlib.Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "w") as f:
        for c in picked:
            f.write(json.dumps(c) + "\n")

    fams = {c["family"] for c in picked}
    vs = collections.Counter(c["verdict"] for c in picked)
    ts = sorted(c["portfolio_s"] for c in picked)
    print(f"{len(picked)} instances across {len(fams)} families -> {a.out}")
    print(f"  verdicts {dict(vs)}; portfolio time median {ts[len(ts)//2]:.0f}s, "
          f"range {ts[0]:.0f}-{ts[-1]:.0f}s")
    print(f"  families with only one usable instance: "
          f"{sum(1 for f in fams if sum(1 for c in picked if c['family'] == f) == 1)}")

    if a.extract:
        d = pathlib.Path(a.extract)
        d.mkdir(parents=True, exist_ok=True)
        n = 0
        for c in picked:
            out = d / (c["hash"] + ".cnf")
            if out.exists():
                continue
            with lzma.open(c["xz_path"]) as src, open(out, "wb") as dst:
                dst.write(src.read())
            n += 1
        print(f"  extracted {n} new .cnf into {d} ({len(picked)} total)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
