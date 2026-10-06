#!/usr/bin/env python3
"""How much faster this machine runs a solver than the SAT Competition's
machines did: time a competition solver here on instances where its official
times are known, and compare.  The solver's search does not depend on time,
so with the same source and the same floating-point rules (no FMA
contraction) it takes the same steps here, and the ratio of times is the
hardware's.

    tools/gbd/speed_calibration.py select     # stratified sample -> OUT/sample.json
    tools/gbd/speed_calibration.py run        # time it -> OUT/results.jsonl
    tools/gbd/speed_calibration.py report

Defaults reproduce the 2026-10-06 calibration against SC2022's anniversary
track: kissat at tag sc2022-bulky, built with gcc in the satsuma image and run
in it like the duo run's satsuma jobs, each instance started only while the
duo run holds at most 9 jobs (lower its cores to 9 first), so the machine
carries the same 10 single-threaded jobs as during the run.  Build first:

    git -C ~/projects/kissat archive sc2022-bulky | tar -x -C OUT/lsrc
    docker run --rm -v OUT/lsrc:/k satsuma-iter-kissat bash -c \\
      'cd /k && CC="gcc -ffp-contract=off" ./configure --competition && make -C build'
"""
import argparse
import csv
import json
import math
import random
import shutil
import statistics
import subprocess
import time
from pathlib import Path

B = Path("/Users/greg/projects/sat_benchmarks")


def select(args, out):
    recs = {json.loads(l)["hash"]: json.loads(l) for l in open(args.index) if l.strip()}
    ref = list(csv.DictReader(open(args.reference)))
    rng = random.Random(args.seed)
    cand = []
    for r in ref:
        t, rec = float(r[args.solver]), recs.get(r["hash"])
        if rec and 30 <= t < 1000 and (rec.get("nclauses") or 0) <= 3_000_000 and list(B.glob(f"{r['hash']}-*.cnf.xz")):
            cand.append((t, r["hash"], rec.get("family", "?"), r.get("verified-result", "")))
    rng.shuffle(cand)
    pick, fams = [], set()
    for lo, hi, n in ((30, 100, 7), (100, 300, 7), (300, 1000, 6)):
        k = 0
        for t, h, fam, v in cand:
            if lo <= t < hi and fam not in fams and k < n:
                pick.append(dict(hash=h, name=recs[h]["filename"].replace(".cnf.xz", ""), family=fam,
                                 t2022=t, status=v, nclauses=recs[h].get("nclauses")))
                fams.add(fam)
                k += 1
    json.dump(pick, open(out / "sample.json", "w"), indent=1)
    print(f"{len(pick)} instances, official total {sum(p['t2022'] for p in pick):.0f} s -> {out / 'sample.json'}")


def run(args, out):
    res = out / "results.jsonl"
    done = {json.loads(l)["hash"] for l in open(res)} if res.exists() else set()
    running = Path(args.duo_run) / "running.json"

    def duo_jobs():
        try:
            return len(json.load(open(running)))
        except (OSError, ValueError):
            return 99

    for s in json.load(open(out / "sample.json")):
        h = s["hash"]
        if h in done:
            continue
        while duo_jobs() > args.max_duo_jobs:
            time.sleep(5)
        # A fresh directory per instance: Docker Desktop's file sharing can
        # serve a stale view of a file recreated under the same name.
        w = Path("/tmp/speed_calibration") / h
        shutil.rmtree(w, ignore_errors=True)
        w.mkdir(parents=True)
        xz = next(iter(sorted(B.glob(f"{h}-*.cnf.xz"))))
        with open(w / "f.cnf", "wb") as f:
            subprocess.run(["xz", "-dc", str(xz)], stdout=f, check=True)
        cap = int(min(2 * s["t2022"] + 60, 2000))
        inner = (f'TIMEFORMAT="%R %U %S"; {{ time timeout {cap} /k/kissat /work/f.cnf > /work/out.txt; }} '
                 '2> /work/time.txt; echo rc=$?')
        t0 = time.time()
        subprocess.run(["docker", "run", "--rm", "-v", f"{w}:/work", "-v", f"{Path(args.build).resolve()}:/k:ro",
                        args.image, "bash", "-c", inner], capture_output=True, text=True, timeout=cap + 300)
        rec = dict(s, cap=cap, host_wall=round(time.time() - t0, 2), jobs_at_start=duo_jobs())
        try:
            real, user, sys_ = (float(x) for x in (w / "time.txt").read_text().split()[-3:])
            rec.update(real=real, user=user, sys=sys_)
        except (OSError, ValueError) as e:
            rec["error"] = str(e)
        v = [l for l in (w / "out.txt").read_text().splitlines() if l.startswith("s ")] if (w / "out.txt").exists() else []
        rec["verdict"] = v[0][2:] if v else "none"
        shutil.rmtree(w, ignore_errors=True)
        with open(res, "a") as f:
            f.write(json.dumps(rec) + "\n")
        print(f"{s['name'][:44]:44s} official {s['t2022']:7.1f}  here {rec.get('real', 0):7.1f}  {rec['verdict']}", flush=True)


def report(args, out):
    rs = [json.loads(l) for l in open(out / "results.jsonl")]
    rs = [r for r in rs if "real" in r]
    agree = all(r["verdict"] in ("SATISFIABLE", "UNSATISFIABLE") and (r["verdict"] == "SATISFIABLE") == (r["status"] == "sat")
                for r in rs)
    k = sorted(r["t2022"] / r["real"] for r in rs)
    q = lambda p: k[int(round(p * (len(k) - 1)))]
    print(f"{len(rs)} instances, verdicts as recorded: {agree}")
    print(f"official time / time here: median {statistics.median(k):.2f}, geometric mean "
          f"{math.exp(statistics.mean(map(math.log, k))):.2f}, quartiles {q(.25):.2f}-{q(.75):.2f}, range {k[0]:.2f}-{k[-1]:.2f}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("step", choices=("select", "run", "report"))
    ap.add_argument("--out", default="speed_calibration")
    ap.add_argument("--index", default=str(B / "anni_2022.jsonl"))
    ap.add_argument("--reference", default=str(B / "sc2022" / "anni-seq.csv"))
    ap.add_argument("--solver", default="kissat-sc2022-bulky", help="the reference column the build reproduces")
    ap.add_argument("--seed", type=int, default=20261006)
    ap.add_argument("--build", default="speed_calibration/lsrc/build", help="directory holding the kissat binary")
    ap.add_argument("--image", default="satsuma-iter-kissat")
    ap.add_argument("--duo-run", default=str(B / "runs" / "anni_2022_duo"))
    ap.add_argument("--max-duo-jobs", type=int, default=9)
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    {"select": select, "run": run, "report": report}[args.step](args, out)


if __name__ == "__main__":
    main()
