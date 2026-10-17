#!/usr/bin/env python3
"""Decide, exactly, whether any archived cyclic scheme (symenumd
workdirs) has per-step <= 50.  Per-step = 3a+14, so the question is
whether the A-leg cost a is <= 12.  With d distinct nonzero rows the
floor is d-9, so each scheme gets the cheapest fbmin mode that decides
a <= 12:
  d >= 22  floor >= 13, no search needed
  d  = 21  a <= 12 iff the floor is attained: --tier1-only
  d  = 20  a <= 12 iff floor or floor+1: default (tiers 1-2)
  d <= 19  --tier3 (exact up to floor+2; undecided below d = 19)
Every scheme is first re-verified against the full Brent system,
schemes are deduplicated across workdirs by canonical summand set, and
each row is written as soon as it is decided.

Usage: symcheck.py fbmin out.csv workdir [workdir ...] [--jobs N]
"""
import csv
import os
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from brent import brent_equations  # noqa: E402
from equiv import bits_to_summands  # noqa: E402

args = sys.argv[1:]
JOBS = 8
if "--jobs" in args:
    k = args.index("--jobs")
    JOBS = int(args[k + 1])
    del args[k:k + 2]
FBMIN, OUT, DIRS = args[0], args[1], args[2:]
LEG_RE = re.compile(r"min_adds(>?=)(\d+)")
EQS = list(brent_equations(3, 3, 3, 23))


def leg_stats(bits):
    rows = ["".join(str(bits[9 * m + k]) for k in range(9)) for m in range(23)]
    uniq = sorted({r for r in rows if r != "0" * 9})
    s = {int(r, 2) for r in uniq}
    ints = sorted(s)
    tri = set()
    for i, a in enumerate(ints):
        for b in ints[i + 1:]:
            if a ^ b in s:
                tri |= {a, b, a ^ b}
    return uniq, len(uniq), len(ints) - len(tri)


def fbmin(rows, flags):
    with tempfile.NamedTemporaryFile("w", suffix=".legs", delete=False) as f:
        f.write("\n".join(rows) + "\n")
        path = f.name
    try:
        return subprocess.run([FBMIN, *flags, "--threads", "1", path],
                              capture_output=True, text=True).stdout
    finally:
        os.unlink(path)


def check(item):
    src, bits = item
    uniq, d, iso = leg_stats(bits)
    if d >= 22:
        return (src, d, iso, "floor", f">={d - 9}", "no")
    flags = {21: ["--tier1-only"], 20: []}.get(d, ["--tier3"])
    o = fbmin(uniq, flags)
    m = LEG_RE.search(o)
    if not m:
        raise RuntimeError(f"{src}: unexpected fbmin output: {o[:200]}")
    a = int(m.group(2))
    if m.group(1) == "=":
        leg, verdict = str(a), ("YES" if a <= 12 else "no")
    else:
        leg, verdict = f">={a}", ("no" if a >= 13 else "undecided")
    return (src, d, iso, " ".join(flags) or "tiers1-2", leg, verdict)


def brent_ok(bits):
    for mons, rhs in EQS:
        acc = 0
        for (x, y, z) in mons:
            acc ^= bits[x] & bits[y] & bits[z]
        if acc != rhs:
            return False
    return True


def items():
    seen = set()
    for wd in DIRS:
        for name in sorted(os.listdir(wd)):
            if not (name.startswith("sym-") and name.endswith(".bits")):
                continue
            with open(os.path.join(wd, name)) as f:
                bits = [int(c) for c in f.read().strip()]
            assert len(bits) == 621 and brent_ok(bits), f"{wd}/{name}: not a scheme"
            key = tuple(sorted(bits_to_summands(bits)))
            if key in seen:
                continue
            seen.add(key)
            yield (f"{os.path.basename(os.path.normpath(wd))}/{name}", bits)


if __name__ == "__main__":
    rows = []
    with ProcessPoolExecutor(JOBS) as ex, open(OUT, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["scheme", "d", "iso", "fbmin_mode", "leg", "perstep_le_50"])
        f.flush()
        for r in ex.map(check, list(items())):
            rows.append(r)
            w.writerow(r)
            f.flush()
    print(f"distinct cyclic schemes: {len(rows)}")
    for d in sorted({r[1] for r in rows}):
        sub = [r for r in rows if r[1] == d]
        legs = sorted({r[4] for r in sub})
        print(f"  d={d}: {len(sub)} schemes, legs {legs}")
    for v in ("YES", "undecided"):
        hit = [r for r in rows if r[5] == v]
        print(f"per-step <= 50 {v}: {len(hit)}")
        for r in hit:
            print("  ", r)
