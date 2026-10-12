#!/usr/bin/env python3
"""Sweep OUR novel-scheme corpus with fbmin (tiers 1-3) -- the same
verdict logic as fbsweep.py, over pre-emitted .legs files (from
dprofile_bits.py).  ALERT when exact leg minima sum <= 37 (per-step
total <= 51); tie-52 at 38.

Usage: fbsweep_ours.py legsdir fbmin out.csv threads name [name ...]
"""
import pathlib, re, subprocess, sys, time

LEGS, FBMIN, OUT, THREADS = sys.argv[1:5]
NAMES = sys.argv[5:]
LEGS = pathlib.Path(LEGS)
RE = re.compile(r"min_adds(>?=)(\d+) \[(.*?)\]")

done = set()
out = pathlib.Path(OUT)
if out.exists():
    done = {ln.split(",")[0] for ln in out.read_text().splitlines()[1:]}
else:
    out.write_text("name,legA,legB,legC,sum,verdict,secs\n")

for name in NAMES:
    if name in done:
        continue
    t0 = time.time()
    vals = []
    for nm in "ABC":
        r = subprocess.run(
            [FBMIN, "--tier3", "--threads", THREADS, str(LEGS / f"{name}_{nm}.legs")],
            capture_output=True, text=True, timeout=2400)
        m = RE.search(r.stdout)
        assert m, r.stdout[:200]
        vals.append(("=" if m.group(1) == "=" else ">=") + m.group(2))
    secs = time.time() - t0
    nums = [int(v.lstrip(">=")) for v in vals]
    exact = all(v.startswith("=") for v in vals)
    s = sum(nums)
    if exact and s <= 37:
        verdict = f"ALERT-{s + 14}"
    elif exact and s == 38:
        verdict = "tie-52"
    elif not exact and s > 37:
        verdict = "ruled-out-51"
    elif exact:
        verdict = f"total-{s + 14}"
    else:
        verdict = "undecided"
    with open(out, "a") as f:
        f.write(f"{name},{vals[0]},{vals[1]},{vals[2]},{s},{verdict},{secs:.0f}\n")
    print(f"{name}: legs={vals} sum{'=' if exact else '>='}{s} -> {verdict} "
          f"({secs:.0f} s)", flush=True)
    if verdict.startswith("ALERT"):
        print(f"*** ALERT: {name} (OUR class) per-step {s + 14} ***", flush=True)
print("ours sweep complete.", flush=True)
