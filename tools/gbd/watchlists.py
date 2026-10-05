#!/usr/bin/env python3
"""How satsuma is doing, in a duo run, on the instances behind each idea in
doc/ideas_watchlist.md: reached so far, solved, failed (each failure makes
the idea more promising), with the 2022 field's record beside each failure.

    tools/gbd/watchlists.py                       # the anniversary run
    tools/gbd/watchlists.py --run RUN --lists tools/gbd/watchlists_anni_2022.json
"""
import argparse
import csv
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
B = Path("/Users/greg/projects/sat_benchmarks")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--run", default=str(B / "runs" / "anni_2022_duo"))
    ap.add_argument("--lists", default=str(HERE / "watchlists_anni_2022.json"))
    ap.add_argument("--reference", default=str(B / "sc2022" / "anni-seq.csv"))
    ap.add_argument("--source", default="satsuma", help="the backend whose failures matter")
    args = ap.parse_args()
    run = Path(args.run)
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

    lists = json.load(open(args.lists))
    others = [b for b in cfg["backends"] if b != args.source]
    for idea, hs in lists.items():
        reached = [h for h in hs if (h, args.source) in res]
        failed = [h for h in reached if res[(h, args.source)]["result"] not in ("SAT", "UNSAT")]
        nxt = sorted((h for h in hs if (h, args.source) not in res), key=lambda h: pos.get(h, 10**9))
        print(f"{idea}: {len(hs)} instances; {args.source} reached {len(reached)}, solved {len(reached) - len(failed)}, "
              f"failed {len(failed)}" + (f"; next at #{pos[nxt[0]]}" if nxt else "; all reached"))
        for h in sorted(failed, key=lambda h: pos.get(h, 0)):
            r = res[(h, args.source)]
            oth = "; ".join(f"{b} {res[(h, b)]['result']}" for b in others if (h, b) in res)
            print(f"    #{pos.get(h, '?'):<5} {r['name'][:46]:46s} {args.source} {r['result']:8s} {field(h):22s} {oth}")


if __name__ == "__main__":
    main()
