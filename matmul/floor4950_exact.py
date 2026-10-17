#!/usr/bin/env python3
"""Rigorous check that no database scheme at KS floor 49 or 50 can host
a per-step 50.  A 50 leaves slack 50 - floor across the three legs, so
a floor-49 scheme needs at least two legs that attain their floor d-9,
and a floor-50 scheme needs all three.  A leg attains its floor iff
some 9-target basis closes over all targets (fbmin --tier1-only, an
exhaustive test).  Each scheme stops at the first leg that rules it
out.

Usage: floor4950_exact.py schemes.tgz fbmin out.csv [--jobs N]
"""
import csv
import os
import subprocess
import sys
import tarfile
import tempfile
from concurrent.futures import ProcessPoolExecutor

TGZ, FBMIN, OUT = sys.argv[1:4]
JOBS = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 12


def legs_of(text):
    cur, prods = [], []
    for ln in text.splitlines():
        if "|" not in ln:
            continue
        parts = [p.split() for p in ln.split("|")]
        if len(parts) != 3 or any(len(g) != 3 for g in parts):
            continue
        cur.append([[abs(int(v)) % 2 for v in g] for g in parts])
        if len(cur) == 3:
            prods.append(cur)
            cur = []
    if len(prods) != 23:
        return None
    out = []
    for s in range(3):
        rows = {"".join(str(prods[p][r][s][c]) for r in range(3) for c in range(3))
                for p in range(23)}
        rows.discard("0" * 9)
        out.append(sorted(rows))
    return out


def attains_floor(rows):
    with tempfile.NamedTemporaryFile("w", suffix=".legs", delete=False) as f:
        f.write("\n".join(rows) + "\n")
        path = f.name
    try:
        o = subprocess.run([FBMIN, "--tier1-only", "--threads", "1", path],
                           capture_output=True, text=True).stdout
    finally:
        os.unlink(path)
    if "min_adds=" in o and "tier1: 9-target basis closes" in o:
        return True
    if "tier1 exhausted" in o:
        return False
    raise RuntimeError(f"unexpected fbmin output: {o[:200]}")


def check(item):
    name, text = item
    L = legs_of(text)
    if L is None:
        return None
    floor = sum(len(V) for V in L) - 13
    if floor not in (49, 50):
        return None
    need = 2 if floor == 49 else 3
    hits, misses = 0, 0
    for V in L:
        if attains_floor(V):
            hits += 1
        else:
            misses += 1
        if misses > 3 - need:
            break
    return (name, floor, hits, hits >= need)


def items():
    tf = tarfile.open(TGZ, "r:gz")
    for m in tf:
        if m.name.endswith(".tab"):
            yield (m.name.rsplit("/", 1)[-1], tf.extractfile(m).read().decode())


if __name__ == "__main__":
    n, viol = 0, []
    with ProcessPoolExecutor(JOBS) as ex, open(OUT, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["scheme", "floor", "floor_legs_seen", "could_host_50"])
        for r in ex.map(check, items(), chunksize=64):
            if r is None:
                continue
            n += 1
            w.writerow(r)
            if r[3]:
                viol.append(r)
    print(f"floor-49/50 schemes checked: {n}")
    print(f"schemes with enough floor-attaining legs to host a 50: {len(viol)}")
    for r in viol[:20]:
        print("  ", r)
