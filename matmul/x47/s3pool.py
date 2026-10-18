#!/usr/bin/env python3
"""Worker pool over S3-quotient shapes for rank-r <4,4,4> schemes over F2.

Each job is (shape, solver, seed) with a wall cap; solve times are
heavy-tailed, so shapes are revisited with fresh seeds round after round
(cadical and kissat alternating).  SAT models are decoded and verified
against all 4096 Brent equations (s3cnf.decode) and saved; an UNSAT
verdict settles the shape (no S3-invariant scheme of that shape).

Usage: s3pool.py OUTDIR [--rank 47] [--workers 10] [--cap 1200]
                 [--hours 6] [--near 4,8,0,1]
Log: OUTDIR/pool.log (one line per finished job); solutions OUTDIR/sol_*.bits
"""
import argparse
import concurrent.futures as cf
import itertools
import pathlib
import subprocess
import sys
import threading
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import s3cnf  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    ap.add_argument("--rank", type=int, default=47)
    ap.add_argument("--workers", type=int, default=10)
    ap.add_argument("--cap", type=int, default=1200)
    ap.add_argument("--hours", type=float, default=6.0)
    ap.add_argument("--near", default="4,8,0,1")
    args = ap.parse_args()
    out = pathlib.Path(args.outdir)
    (out / "cnf").mkdir(parents=True, exist_ok=True)
    near = tuple(int(x) for x in args.near.split(","))
    shapes = [s for s in itertools.product(range(8), range(17), range(7), range(9))
              if 6 * s[0] + 3 * s[1] + 2 * s[2] + s[3] == args.rank]
    shapes.sort(key=lambda s: (sum(abs(x - y) for x, y in zip(s, near)), s))
    deadline = time.time() + args.hours * 3600
    lock = threading.Lock()
    settled = set()
    log = open(out / "pool.log", "a", buffering=1)

    def say(msg):
        with lock:
            log.write(time.strftime("%H:%M:%S ") + msg + "\n")
            print(time.strftime("%H:%M:%S ") + msg, flush=True)

    def cnf_for(s):
        f = out / "cnf" / ("s4_%d_%d_%d_%d.cnf" % s)
        with lock:
            if not f.exists():
                s3cnf.write_cnf(4, *s, str(f), False)
        return f

    def job(s, solver, seed):
        if time.time() > deadline or s in settled:
            return
        f = cnf_for(s)
        if open(f).readline().startswith("c structurally UNSAT"):
            settled.add(s)
            say(f"UNSAT shape {s} (structural)")
            return
        tag = "%d_%d_%d_%d_%s%d" % (*s, solver[0], seed)
        res = out / f"run_{tag}.out"
        cap = int(min(args.cap, max(1, deadline - time.time())))
        cmd = ["timeout", str(cap), solver, f"--seed={seed}", "-q", str(f)]
        t0 = time.time()
        with open(res, "w") as fh:
            rc = subprocess.run(cmd, stdout=fh, stderr=subprocess.STDOUT).returncode
        dt = time.time() - t0
        if rc == 10:
            bits = out / f"sol_{tag}.bits"
            try:
                s3cnf.decode(4, *s, str(res), str(bits))
                say(f"SAT shape {s} by {solver} seed {seed} in {dt:.0f}s -> {bits.name} (Brent verified)")
            except SystemExit as e:
                say(f"DECODE FAILURE shape {s} {solver} seed {seed}: {e}")
        elif rc == 20:
            settled.add(s)
            say(f"UNSAT shape {s} by {solver} seed {seed} in {dt:.0f}s")
            res.unlink()
        else:
            say(f"timeout shape {s} {solver} seed {seed} ({dt:.0f}s)")
            res.unlink()

    def jobs():
        for rnd in itertools.count():
            solver = "cadical" if rnd % 2 == 0 else "kissat"
            for s in shapes:
                yield s, solver, 100 + rnd

    say(f"pool: rank {args.rank}, {len(shapes)} shapes (nearest {near} first), "
        f"{args.workers} workers, cap {args.cap}s, {args.hours} h")
    with cf.ThreadPoolExecutor(args.workers) as ex:
        pending = set()
        for item in jobs():
            if time.time() > deadline or len(settled) == len(shapes):
                break
            if item[0] in settled:
                continue
            while len(pending) >= args.workers:
                done, pending = cf.wait(pending, return_when=cf.FIRST_COMPLETED)
            pending.add(ex.submit(job, *item))
        cf.wait(pending)
    say(f"pool done: {len(settled)} shapes settled UNSAT")


if __name__ == "__main__":
    main()
