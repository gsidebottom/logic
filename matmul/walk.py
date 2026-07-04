#!/usr/bin/env python3
"""Neighborhood-walk scheme discovery (HKS method 2, compounding).

Maintains a pool of verified schemes (seed files + everything found so
far), repeatedly: pick a random pool scheme, fix a random `nfix`-subset of
its bits, let the native-ANF solver complete the rest, canon-dedupe the
completions against the archive; genuinely new schemes join the pool.

Every accepted scheme is re-verified against the Brent equations by
canon-key machinery (verify_bits) — independent of the solver.

Usage:
  python3 walk.py --minutes 5 [--nfix 300] [--runs 8] [--threads 1]
                  [--seeds seeds] [--archive found] [--anf ../target/release/anf]
"""
import argparse
import glob
import os
import random
import subprocess
import sys
import time

from brent import verify_bits
from canon import canon_key

DIMS = (3, 3, 3, 23)  # default; override with --dims


def load_pool(paths, dims):
    pool = {}
    for p in paths:
        s = open(p).read().split()[-1].strip()
        bits = [int(c) for c in s]
        assert verify_bits(bits, *dims) == 0, f"{p} does not verify"
        pool[canon_key(bits, *dims)] = s
    return pool


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--minutes", type=float, default=5.0)
    ap.add_argument("--dims", default="3,3,3,23",
                    help="n1,n2,n3,r (e.g. 4,4,4,47)")
    ap.add_argument("--nfix", type=int, default=0,
                    help="bits frozen per hop (0 = 48%% of nvars)")
    ap.add_argument("--runs", type=int, default=8, help="completions per hop")
    ap.add_argument("--secs", type=float, default=15.0, help="budget per run")
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--seeds", default="seeds")
    ap.add_argument("--archive", default="found")
    ap.add_argument("--anf", default="../target/release/anf")
    ap.add_argument("--anf-args", default="",
                    help="extra flags passed through to the solver, e.g. "
                    "'--probsat --cb 2.5 --density 0.1 --closure-every 2048'")
    ap.add_argument("--rng", type=int, default=0)
    args = ap.parse_args()

    dims = tuple(int(x) for x in args.dims.split(","))
    from brent import var_counts
    nvars = sum(var_counts(*dims))
    if args.nfix == 0:
        args.nfix = int(nvars * 0.48)
    os.makedirs(args.archive, exist_ok=True)
    seed_files = sorted(glob.glob(f"{args.seeds}/*.bits"))
    arch_files = sorted(glob.glob(f"{args.archive}/*.bits"))
    pool = load_pool(seed_files, dims)
    nseeds = len(pool)
    pool.update(load_pool(arch_files, dims))
    print(f"pool: {nseeds} seeds + {len(pool) - nseeds} archived "
          f"(dims {dims}, nvars {nvars}, nfix {args.nfix})")

    rng = random.Random(args.rng)
    t0 = time.time()
    hops = runs = found = ndup = ntimeout = 0
    keys = list(pool)
    while time.time() - t0 < args.minutes * 60:
        hops += 1
        seed_bits = pool[keys[rng.randrange(len(keys))]]
        tmp = f"/tmp/walk-seed-{os.getpid()}.bits"
        open(tmp, "w").write(seed_bits + "\n")
        for _ in range(args.runs):
            if time.time() - t0 > args.minutes * 60:
                break
            runs += 1
            r = subprocess.run(
                [args.anf, *[str(x) for x in dims], "--fix-file", tmp,
                 "--nfix", str(args.nfix), "--seconds", str(args.secs),
                 "--threads", str(args.threads),
                 "--seed", str(rng.randrange(1 << 30)), "--quiet",
                 *args.anf_args.split()],
                capture_output=True, text=True)
            if "s UNKNOWN" in r.stdout:
                ntimeout += 1
            for line in r.stdout.splitlines():
                if not line.startswith("b "):
                    continue
                s = line[2:].strip()
                bits = [int(c) for c in s]
                if verify_bits(bits, *dims) != 0:
                    print("SOLVER BUG: unverified scheme dropped")
                    continue
                k = canon_key(bits, *dims)
                if k in pool:
                    ndup += 1
                    continue
                pool[k] = s
                keys.append(k)
                found += 1
                out = f"{args.archive}/walk-{len(pool):05d}.bits"
                open(out, "w").write(s + "\n")
                el = time.time() - t0
                print(f"[{el:6.1f}s] NEW scheme #{found} "
                      f"(support {sum(bits)}) -> {out}", flush=True)
    el = time.time() - t0
    print(f"done: {found} new schemes in {el:.0f}s "
          f"({hops} hops, {runs} runs = {found} new + {ndup} dup + "
          f"{ntimeout} timeout"
          f"{f', {el / found:.0f}s/scheme' if found else ''})")


if __name__ == "__main__":
    main()
