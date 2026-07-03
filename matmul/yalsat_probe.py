#!/usr/bin/env python3
"""Bounded yalsat probes; writes one summary line per run."""
import subprocess, time, sys, os

os.chdir(os.path.dirname(os.path.abspath(__file__)))
RUNS = []
for s in (1, 2, 3):
    RUNS.append((f"fix300-s{s}", f"inst/n3r23-fix300-s{s}.cnf", 300))
    RUNS.append((f"fix250-s{s}", f"inst/n3r23-fix250-s{s}.cnf", 300))
RUNS += [
    ("plain-n3r23", "inst/n3r23.cnf", 300),
    ("chal1-2222A", "challenges/challenge1/MM-23-2-2-2-2-A.cnf", 300),
    ("chal1-2222M", "challenges/challenge1/MM-23-2-2-2-2-M.cnf", 300),
    ("chal1-44441", "challenges/challenge1/MM-23-4-4-4-4-1.cnf", 300),
]

for name, path, cap in RUNS:
    t0 = time.time()
    try:
        p = subprocess.run(["./yalsat-bin", path, "1"], capture_output=True,
                           text=True, timeout=cap)
        dt = time.time() - t0
        res = "SAT" if "s SATISFIABLE" in p.stdout else "??"
        # last reported flip rate line
        rate = [l for l in p.stdout.splitlines() if "flips" in l][-1:] 
        print(f"{name}: {res} {dt:.2f}s", flush=True)
    except subprocess.TimeoutExpired:
        print(f"{name}: TIMEOUT {cap}s", flush=True)
print("DONE", flush=True)
