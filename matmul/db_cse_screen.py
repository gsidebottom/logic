#!/usr/bin/env python3
"""CSE-screen the full HKS database: cheap greedy pass per scheme,
checkpointed; the top of the leaderboard then deserves high-effort runs.

Nobody has published addition-optimized counts for the 17,376 DB schemes
(Stapleton's 60-add scheme turns out to be equivalent to DB
i2w201c26fi-000). Cost model: binary +/- counted, negation free, no
basis change — same as slp.py / Martensson-Wagner / Stapleton.

Usage:
  python3 db_cse_screen.py [--workers 6] [--models 2] [--restarts 6]
                           [--hours 6] [--out dbcache/cse_screen.csv]
Resumable: schemes already in the output CSV are skipped.
"""
import argparse
import csv
import os
import sys
import time
from multiprocessing import Pool

from slp import best_cse

M = os.path.dirname(os.path.abspath(__file__))


def work(job):
    name, bs, nmodels, restarts = job
    bits = [int(c) for c in bs]
    try:
        res = best_cse(bits, nmodels, restarts, seed=hash(name) & 0xffff)
        if res is None:
            return (name, -1, "unliftable")
        tot, parts, mi = res
        return (name, tot, f"{parts[0]}+{parts[1]}+{parts[2]}:m{mi}")
    except Exception as e:  # never kill the pool
        return (name, -2, f"error:{e}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--models", type=int, default=2)
    ap.add_argument("--restarts", type=int, default=6)
    ap.add_argument("--hours", type=float, default=6.0)
    ap.add_argument("--out", default="dbcache/cse_screen.csv")
    args = ap.parse_args()
    os.chdir(M)

    done = set()
    if os.path.exists(args.out):
        for row in csv.reader(open(args.out)):
            if row:
                done.add(row[0])
    out = open(args.out, "a", buffering=1)
    w = csv.writer(out)

    jobs = []
    for ln in open("dbcache/all_schemes.txt"):
        name, bs = ln.split()
        if name not in done:
            jobs.append((name, bs, args.models, args.restarts))
    print(f"screen: {len(jobs)} schemes to go ({len(done)} done), "
          f"{args.workers} workers, {args.models}x{args.restarts} "
          f"per scheme, cap {args.hours}h", flush=True)

    t0 = time.time()
    best_seen = 10 ** 9
    n = 0
    with Pool(args.workers) as pool:
        for name, tot, detail in pool.imap_unordered(work, jobs, 8):
            w.writerow([name, tot, detail])
            n += 1
            if 0 < tot < best_seen:
                best_seen = tot
                print(f"[{(time.time()-t0)/60:6.1f}m {n}] new best "
                      f"{tot} adds: {name} ({detail})", flush=True)
            if n % 500 == 0:
                print(f"[{(time.time()-t0)/60:6.1f}m] {n} screened, "
                      f"best {best_seen}", flush=True)
            if time.time() - t0 > args.hours * 3600:
                print("wall cap hit", flush=True)
                pool.terminate()
                break
    print(f"screen wave done: {n} schemes, best {best_seen}", flush=True)


if __name__ == "__main__":
    main()
