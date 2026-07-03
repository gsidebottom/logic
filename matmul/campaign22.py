#!/usr/bin/env python3
"""r=22 campaign: long bounded sweep of drop-a-product repair attacks
(plus a fraction of plain from-scratch attacks) over every scheme we hold.

Each attack: pick a random (scheme, dropped product m, nfix); build the
594-bit wounded seed; run the native solver with closure; log one CSV row
(scheme, m, nfix, secs, best, solved). Append-only log doubles as the
checkpoint — completed (scheme, m, nfix, rng) combos are skipped on
resume. Any SATISFIABLE result is re-verified against the r=22 Brent
system and saved to <outdir>/R22-SOLUTION-<n>.bits with a loud banner.

Hard-bounded: exits after --hours wall-clock; each attack bounded by
--secs via the solver's own budget.

Usage:
  python3 campaign22.py --hours 3 --threads 6 --secs 45 [--plain-frac 0.1]
"""
import argparse
import glob
import os
import random
import subprocess
import sys
import time

from brent import verify_bits
from drop22 import drop_product

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hours", type=float, default=3.0)
    ap.add_argument("--threads", type=int, default=6)
    ap.add_argument("--secs", type=float, default=45.0)
    ap.add_argument("--plain-frac", type=float, default=0.1)
    ap.add_argument("--plain-secs", type=float, default=120.0)
    ap.add_argument("--nfix", default="250,280,300,320")
    ap.add_argument("--outdir", default="found22")
    ap.add_argument("--anf", default="../target/release/anf")
    ap.add_argument("--rng", type=int, default=0)
    args = ap.parse_args()

    os.chdir(HERE)
    os.makedirs(args.outdir, exist_ok=True)
    log_path = f"{args.outdir}/campaign.log"
    done = set()
    if os.path.exists(log_path):
        for line in open(log_path):
            done.add(",".join(line.split(",")[:4]))
    log = open(log_path, "a", buffering=1)

    schemes = sorted(glob.glob("seeds/*.bits") + glob.glob("found/*.bits"))
    pool = []
    for p in schemes:
        s = open(p).read().split()[-1].strip()
        bits = [int(c) for c in s]
        if verify_bits(bits, 3, 3, 3, 23) == 0:
            pool.append((os.path.basename(p)[:-5], bits))
    nfixes = [int(x) for x in args.nfix.split(",")]
    print(f"campaign22: {len(pool)} verified 23-schemes, "
          f"{len(done)} attacks already logged, "
          f"{args.hours}h x {args.threads} threads", flush=True)

    rng = random.Random(args.rng)
    t0 = time.time()
    n = best_floor = 10 ** 9
    n = 0
    nsol = 0
    while time.time() - t0 < args.hours * 3600:
        n += 1
        plain = rng.random() < args.plain_frac
        if plain:
            name, m, nfix = "PLAIN", -1, 0
            secs = args.plain_secs
            cmd = [args.anf, "3", "3", "3", "22"]
        else:
            name, bits = pool[rng.randrange(len(pool))]
            m = rng.randrange(23)
            nfix = nfixes[rng.randrange(len(nfixes))]
            secs = args.secs
            key = f"{name},{m},{nfix},{n}"
            if ",".join(key.split(",")[:4]) in done:
                continue
            v22 = drop_product(bits, m)
            seedf = f"/tmp/c22-{os.getpid()}.bits"
            open(seedf, "w").write("".join(map(str, v22)) + "\n")
            cmd = [args.anf, "3", "3", "3", "22", "--fix-file", seedf,
                   "--nfix", str(nfix)]
        cmd += ["--probsat", "--cb", "2.5", "--density", "0.1",
                "--closure-every", "2048", "--seconds", str(secs),
                "--threads", str(args.threads),
                "--seed", str(rng.randrange(1 << 30)), "--quiet"]
        r = subprocess.run(cmd, capture_output=True, text=True)
        sline = next((l for l in r.stdout.splitlines()
                      if l.startswith("s ")), "s ??")
        solved = "SATISFIABLE" in sline
        best = 0 if solved else int(
            sline.split("best ")[1].split()[0]) if "best " in sline else -1
        log.write(f"{name},{m},{nfix},{n},{secs},{best},{int(solved)}\n")
        if 0 <= best < best_floor:
            best_floor = best
            print(f"[{(time.time()-t0)/60:6.1f}m] attack {n}: "
                  f"new best floor {best} ({name} drop {m} nfix {nfix})",
                  flush=True)
        if solved:
            for l in r.stdout.splitlines():
                if l.startswith("b "):
                    s22 = l[2:].strip()
                    bits22 = [int(c) for c in s22]
                    bad = verify_bits(bits22, 3, 3, 3, 22)
                    nsol += 1
                    out = f"{args.outdir}/R22-SOLUTION-{nsol}.bits"
                    open(out, "w").write(s22 + "\n")
                    print(f"{'!' * 60}\nR22 SCHEME FOUND (verify: {bad} "
                          f"violated) -> {out}\nfrom {name} drop {m} "
                          f"nfix {nfix}\n{'!' * 60}", flush=True)
    print(f"campaign wave done: {n} attacks, best floor {best_floor}, "
          f"{nsol} solutions", flush=True)


if __name__ == "__main__":
    main()
