#!/usr/bin/env python3
"""Enumerate cyclic-invariant rank-23 schemes: solve the symmetric
quotient CNF with kissat, block each solution's 207-rep projection,
repeat.  Every solution is expanded through the orbit map, verified
against the FULL Brent system, archived, and screened on its (single)
leg: per-step = 3a + 14 with a >= d-9, so

    d=21  -> floor a=12 -> 50 candidate (KLAXON check); attaining it
             needs >= 12 rows that are sums of two others (iso <= 9)
    d=20  -> floor a=11 -> as low as 47 (!) if achievable
    d>=22 -> floor >= 13 -> per-step >= 53, no 50 possible

Candidates (d <= 20, or d = 21 with iso <= 9) get fbmin --tier3
immediately.  Superseded by symenumd.py (incremental CaDiCaL).

Usage: symenum.py cnf map workdir fbmin [--max N] [--threads T]
Stop: touch <workdir>/STOP.
"""
import pathlib
import re
import subprocess
import sys
import time

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from brent import brent_equations  # noqa: E402

args = sys.argv[1:]
flags = {"--max": 100000, "--threads": 2}
pos = []
i = 0
while i < len(args):
    if args[i] in flags:
        flags[args[i]] = int(args[i + 1])
        i += 2
    else:
        pos.append(args[i])
        i += 1
CNF0, MAPF, WORKD, FBMIN = pos[0], pos[1], pathlib.Path(pos[2]), pos[3]
WORKD.mkdir(parents=True, exist_ok=True)
RES = WORKD / "symenum_results.csv"
if not RES.exists():
    RES.write_text("n,d,iso,leg,perstep,secs\n")

rep = {}
for ln in open(MAPF):
    v, r = ln.split()
    rep[int(v)] = int(r)
reps = sorted(set(rep.values()))
EQS = list(brent_equations(3, 3, 3, 23))

cnf = pathlib.Path(CNF0).read_text().splitlines()
header = cnf[0].split()
nvars, nclauses = int(header[2]), int(header[3])
clauses = cnf[1:]

LEG_RE = re.compile(r"min_adds(>?=)(\d+)")


def leg_stats(bits):
    rows = ["".join(str(bits[9 * m + k]) for k in range(9)) for m in range(23)]
    uniq = sorted({r for r in rows if r != "0" * 9})
    ints = [int(r, 2) for r in uniq]
    s = set(ints)
    tri = set()
    for a in range(len(ints)):
        for b in range(a + 1, len(ints)):
            if ints[a] ^ ints[b] in s:
                tri |= {ints[a], ints[b], ints[a] ^ ints[b]}
    return uniq, len(uniq), len(ints) - len(tri)


n = 0
while n < flags["--max"] and not (WORKD / "STOP").exists():
    work_cnf = WORKD / "cur.cnf"
    with open(work_cnf, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        f.write("\n".join(clauses) + "\n")
    t0 = time.time()
    r = subprocess.run(["kissat", "-q", str(work_cnf)],
                       capture_output=True, text=True)
    secs = time.time() - t0
    if "s SATISFIABLE" not in r.stdout:
        print(f"ENUMERATION COMPLETE after {n} solutions "
              f"({r.stdout.splitlines()[0] if r.stdout else 'no output'})",
              flush=True)
        break
    vals = {}
    for ln in r.stdout.splitlines():
        if ln.startswith("v "):
            for tok in ln.split()[1:]:
                x = int(tok)
                if x:
                    vals[abs(x)] = 1 if x > 0 else 0
    bits = [vals.get(rep[v] + 1, 0) for v in range(621)]
    bad = 0
    for mons, rhs in EQS:
        acc = 0
        for (x, y, z) in mons:
            acc ^= bits[x] & bits[y] & bits[z]
        bad += (acc != rhs)
    assert bad == 0, f"solution {n} fails full Brent ({bad})"
    n += 1
    out = WORKD / f"sym-{n:05d}.bits"
    out.write_text("".join(map(str, bits)) + "\n")
    uniq, d, iso = leg_stats(bits)
    leg_val, perstep = "", ""
    if d <= 20 or (d == 21 and d - iso >= 12):
        lp = WORKD / f"sym-{n:05d}_A.legs"
        lp.write_text("\n".join(uniq) + "\n")
        try:
            o = subprocess.run(
                [FBMIN, "--tier3", "--threads", str(flags["--threads"]),
                 str(lp)], capture_output=True, text=True,
                timeout=2400).stdout
            m = LEG_RE.search(o)
            if m:
                leg_val = ("=" if m.group(1) == "=" else ">=") + m.group(2)
                if m.group(1) == "=":
                    perstep = 3 * int(m.group(2)) + 14
                    if perstep <= 50:
                        print("!" * 60 + f"\nSYM-KLAXON: per-step {perstep} "
                              f"(leg {leg_val}, d={d}) -> {out}\n" + "!" * 60,
                              flush=True)
        except subprocess.TimeoutExpired:
            leg_val = ">=?"
    print(f"sym-{n:05d}: d={d} iso={iso} leg={leg_val} "
          f"perstep={perstep} ({secs:.0f}s solve)", flush=True)
    with open(RES, "a") as f:
        f.write(f"{n},{d},{iso},{leg_val},{perstep},{secs:.0f}\n")
    # block this solution's rep projection
    block = " ".join(str(-(rv + 1)) if vals.get(rv + 1, 0) else str(rv + 1)
                     for rv in reps) + " 0"
    clauses.append(block)
print("symenum done.", flush=True)
