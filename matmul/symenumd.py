#!/usr/bin/env python3
"""Driver for the incremental Rust enumerator (src/bin/symenum.rs):
consume its stream of `b <621 bits>` lines; for each solution verify
the FULL Brent system, canon-dedup (product relabelings can survive
symmetry breaking), archive, screen the leg (d, isolation), and run
fbmin --tier3 immediately on candidates (d<=21, iso<=2).  Per-step =
3a+14: SYM-KLAXON at <= 50.

Usage: symenumd.py symenum-bin cnf map workdir fbmin [--threads T]
Stop: touch <workdir>/STOP (kills the enumerator).
"""
import pathlib
import re
import subprocess
import sys
import time

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from brent import brent_equations  # noqa: E402
from equiv import bits_to_summands  # noqa: E402

args = sys.argv[1:]
flags = {"--threads": 2}
pos = []
i = 0
while i < len(args):
    if args[i] in flags:
        flags[args[i]] = int(args[i + 1])
        i += 2
    else:
        pos.append(args[i])
        i += 1
ENUM, CNF, MAPF, WORKD, FBMIN = pos[0], pos[1], pos[2], pathlib.Path(pos[3]), pos[4]
WORKD.mkdir(parents=True, exist_ok=True)
RES = WORKD / "symenum_results.csv"
if not RES.exists():
    RES.write_text("n,d,iso,leg,perstep,secs\n")

EQS = list(brent_equations(3, 3, 3, 23))
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


proc = subprocess.Popen([ENUM, CNF, MAPF], stdout=subprocess.PIPE, text=True)
n = 0
seen = set()
t_last = time.time()
for line in proc.stdout:
    line = line.strip()
    if (WORKD / "STOP").exists():
        proc.kill()
        print("STOP present -- enumerator killed.", flush=True)
        break
    if line.startswith("s "):
        print(f"ENUMERATOR: {line}", flush=True)
        break
    if not line.startswith("b "):
        continue
    bits = [int(c) for c in line[2:].strip()]
    assert len(bits) == 621
    secs = time.time() - t_last
    t_last = time.time()
    bad = 0
    for mons, rhs in EQS:
        acc = 0
        for (x, y, z) in mons:
            acc ^= bits[x] & bits[y] & bits[z]
        bad += (acc != rhs)
    assert bad == 0, "solution fails full Brent"
    key = tuple(sorted(bits_to_summands(bits)))
    if key in seen:
        continue
    seen.add(key)
    n += 1
    out = WORKD / f"sym-{n:05d}.bits"
    out.write_text("".join(map(str, bits)) + "\n")
    uniq, d, iso = leg_stats(bits)
    leg_val, perstep = "", ""
    if d <= 21 and iso <= 2:
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
          f"perstep={perstep} ({secs:.0f}s)", flush=True)
    with open(RES, "a") as f:
        f.write(f"{n},{d},{iso},{leg_val},{perstep},{secs:.0f}\n")
print("symenumd done.", flush=True)
