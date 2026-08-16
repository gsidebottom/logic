#!/usr/bin/env python3
"""Streamlined r=22 wound campaign through the satsuma pipeline.

Attack = (scheme, dropped product m, nfix): drop product m from a known
23-scheme, fix all 27 bits of nfix of the remaining 22 products as unit
clauses on the r=22 Brent CNF, hand the wound to hydra_satsuma.
SAT => rank-22 completion (decode + verify + loud banner).
Hard-bounded by --hours; each attack by --secs.

Usage: python3 matmul/r22/wounds.py --hours 3 --secs 90 --workers 3
"""
import argparse, csv, itertools, os, random, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
MM = os.path.dirname(HERE)
sys.path.insert(0, MM)
from drop22 import drop_product
from brent import verify_bits

SAT_BIN = os.path.join(MM, "..", "target", "release", "sat")
BASE_CNF = os.path.join(HERE, "brent_3x3x22.cnf")

SCHEMES = [
    "external/i19-perminov56.bits",
    "external/i106b.bits",
    "external/i107.bits",
    "external/stapleton60.bits",
    "found55/hunt54/reps/i46w213c23ci-016-v2-s26-90_16_11.bits",
    "found55/hunt54/reps/i73w191c236f-000-v3-s26-30_48_92.bits",
]

def load_bits(path):
    return [int(c) for c in open(path).read() if c.isdigit()]

def wound_cnf(bits23, m, nfix, seed, out_path):
    bits22 = drop_product(bits23, m)
    rng = random.Random(seed)
    prods = rng.sample(range(22), nfix)
    units = []
    for k in prods:
        for blk, base in ((0, 0), (1, 198), (2, 396)):
            for j in range(9):
                v = base + k * 9 + j
                units.append(v + 1 if bits22[v] else -(v + 1))
    base = open(BASE_CNF).read().splitlines()
    hdr = base[0].split()
    nv, ncl = int(hdr[2]), int(hdr[3])
    with open(out_path, "w") as f:
        f.write(f"p cnf {nv} {ncl + len(units)}\n")
        f.write("\n".join(base[1:]))
        f.write("\n")
        for u in units:
            f.write(f"{u} 0\n")
    return bits22

def run_attack(args):
    scheme, m, nfix, secs, idx = args
    bits23 = load_bits(os.path.join(MM, scheme))
    cnf = os.path.join(HERE, f"wound_{idx}.cnf")
    wound_cnf(bits23, m, nfix, 1000 + idx, cnf)
    t0 = time.time()
    p = subprocess.run(
        [SAT_BIN, "-b", "hydra_satsuma", "--timeout", str(secs)],
        stdin=open(cnf), capture_output=True, text=True)
    el = time.time() - t0
    res = "TIMEOUT"
    if "s SATISFIABLE" in p.stdout:
        res = "SAT"
        model_path = cnf + ".model"
        with open(model_path, "w") as f:
            f.write(p.stdout)
        print(f"\n*** R22 SAT CANDIDATE: {scheme} drop {m} nfix {nfix} "
              f"-> {model_path} ***\n", flush=True)
    elif "s UNSATISFIABLE" in p.stdout:
        res = "UNSAT"
    os.unlink(cnf)
    return (scheme, m, nfix, round(el, 1), res)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hours", type=float, default=3.0)
    ap.add_argument("--secs", type=int, default=90)
    ap.add_argument("--workers", type=int, default=3)
    a = ap.parse_args()
    grid = []
    idx = 0
    for nfix in (20, 16, 12):
        for scheme in SCHEMES:
            for m in range(23):
                grid.append((scheme, m, nfix, a.secs, idx))
                idx += 1
    deadline = time.time() + a.hours * 3600
    log = csv.writer(open(os.path.join(HERE, "wounds_log.csv"), "a"))
    from concurrent.futures import ThreadPoolExecutor, as_completed
    done = 0
    with ThreadPoolExecutor(max_workers=a.workers) as ex:
        futs = {}
        gi = iter(grid)
        for _ in range(a.workers):
            g = next(gi, None)
            if g: futs[ex.submit(run_attack, g)] = g
        while futs:
            for f in as_completed(list(futs)):
                row = f.result()
                log.writerow(row)
                done += 1
                if done % 20 == 0:
                    print(f"{done} attacks done", flush=True)
                del futs[f]
                if time.time() < deadline:
                    g = next(gi, None)
                    if g: futs[ex.submit(run_attack, g)] = g
                break
    print(f"campaign done: {done} attacks")

if __name__ == "__main__":
    main()
