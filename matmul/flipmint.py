#!/usr/bin/env python3
"""The 50-hunt over the FLIP adjacency: mint50's screen + exact-tier
funnel, with the scheme generator swapped from the ANF-SLS walk to
parallel Kauers-Moosbauer flip walks (flip.py) -- the move set
Stapleton-Perminov's scheme came from, structurally different from
SLS repair, so it reaches basins the SLS walk cannot.

Each batch runs N single-threaded flip.py instances (distinct rngs,
per-instance archives), merges their finds into the main archive
content-deduped (flip.py's canon_key), then screens every new scheme
(floor <= 48, or floor-49 with >= 2 isolation-0 legs, or floor-50
with 3 -- the only shapes that can host a 50) and runs fbmin tiers on
keepers ranked by triple isolation.  ALERT at per-step 51, KLAXON at
<= 50.  A flip walk can also reduce RANK: flip.py saves and shouts
any rank < 23 event (that would be the open problem).

Usage: flipmint.py workdir fbmin [--walkers N] [--threads T]
         [--batch-min M]
Stop: touch <workdir>/STOP.
"""
import pathlib
import re
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).parent))
from canon import canon_key  # noqa: E402
from flip import load as flip_load  # noqa: E402

args = sys.argv[1:]
flags = {"--walkers": 8, "--threads": 8, "--batch-min": 15}
pos = []
i = 0
while i < len(args):
    if args[i] in flags:
        flags[args[i]] = int(args[i + 1])
        i += 2
    else:
        pos.append(args[i])
        i += 1
WORK, FBMIN = pathlib.Path(pos[0]), pos[1]
ARCH = WORK / "archive"
LEGS = WORK / "legs"
RES = WORK / "flipmint_results.csv"
for d in (WORK, ARCH, LEGS):
    d.mkdir(parents=True, exist_ok=True)
if not RES.exists():
    RES.write_text("scheme,floor,isoA,isoB,isoC,legA,legB,legC,sum,verdict,secs\n")

DIMS = (3, 3, 3, 23)


def leg_rows(bits, off):
    return [bits[off + 9 * m: off + 9 * m + 9] for m in range(23)]


def stats(rows):
    uniq = sorted({r for r in rows if r != "0" * 9})
    ints = [int(r, 2) for r in uniq]
    s = set(ints)
    in_tri = set()
    for a in range(len(ints)):
        for b in range(a + 1, len(ints)):
            z = ints[a] ^ ints[b]
            if z in s:
                in_tri |= {ints[a], ints[b], z}
    return len(uniq), len(ints) - len(in_tri), uniq


LEG_RE = re.compile(r"min_adds(>?=)(\d+) \[")


def run_leg(path):
    try:
        out = subprocess.run(
            [FBMIN, "--tier3", "--threads", str(flags["--threads"]), str(path)],
            capture_output=True, text=True, timeout=2400).stdout
    except subprocess.TimeoutExpired:
        return ">=?"
    m = LEG_RE.search(out)
    return (("=" if m.group(1) == "=" else ">=") + m.group(2)) if m else ">=?"


screened = set()
for ln in RES.read_text().splitlines()[1:]:
    screened.add(ln.split(",")[0])

# content keys of everything already in the main archive
known = set()
for p in sorted(ARCH.glob("*.bits")):
    known.add(canon_key(flip_load(str(p), DIMS), *DIMS))

batch = 0
nseq = len(list(ARCH.glob("*.bits")))
while not (WORK / "STOP").exists():
    batch += 1
    print(f"== flip batch {batch} ({flags['--walkers']} walkers x "
          f"{flags['--batch-min']} min) ==", flush=True)
    procs = []
    for w in range(flags["--walkers"]):
        sub = WORK / f"w{w:02d}"
        sub.mkdir(exist_ok=True)
        procs.append(subprocess.Popen(
            [sys.executable, "flip.py", "--dims", "3,3,3,23",
             "--seeds", str(WORK / "seeds"), "--archive", str(sub),
             "--minutes", str(flags["--batch-min"]),
             "--lift-every", "1000000",
             "--rng", str(batch * 100 + w)],
            cwd=pathlib.Path(__file__).parent,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL))
    for p in procs:
        p.wait()
    merged = 0
    for w in range(flags["--walkers"]):
        sub = WORK / f"w{w:02d}"
        for p in sorted(sub.glob("*.bits")):
            if p.name.startswith("RANK"):
                dst = ARCH / f"RANK-{p.name}"
                p.rename(dst)
                print("!" * 60 + f"\nRANK EVENT archived: {dst}\n" + "!" * 60,
                      flush=True)
                continue
            key = canon_key(flip_load(str(p), DIMS), *DIMS)
            if key in known:
                p.unlink()
                continue
            known.add(key)
            dst = ARCH / f"flip-{nseq:05d}.bits"
            nseq += 1
            p.rename(dst)
            merged += 1
    news = []
    for p in sorted(ARCH.glob("flip-*.bits")):
        if p.stem in screened:
            continue
        screened.add(p.stem)
        bits = p.read_text().split()[-1].strip()
        if len(bits) != 621:
            continue
        legs = [leg_rows(bits, off) for off in (0, 207, 414)]
        st = [stats(l) for l in legs]
        floor = sum(x[0] for x in st) - 13
        iso = [x[1] for x in st]
        nclean = sum(1 for x in iso if x == 0)
        if not (floor <= 48 or (floor == 49 and nclean >= 2)
                or (floor == 50 and nclean == 3)):
            continue
        news.append((sum(iso), floor, p.stem, st))
    news.sort()
    print(f"batch {batch}: merged {merged} new schemes, "
          f"{len(news)} keepers", flush=True)
    for toti, floor, stem, st in news:
        if (WORK / "STOP").exists():
            break
        paths = []
        for (d_, i_, uniq), nm in zip(st, "ABC"):
            pp = LEGS / f"{stem}_{nm}.legs"
            pp.write_text("\n".join(uniq) + "\n")
            paths.append(pp)
        t0 = time.time()
        vals = [run_leg(p) for p in paths]
        secs = time.time() - t0
        digs = [v.lstrip(">=") for v in vals]
        if all(x.isdigit() for x in digs):
            ssum = sum(int(x) for x in digs)
            exact = all(v.startswith("=") for v in vals)
            if exact and ssum <= 36:
                verdict = f"KLAXON-{ssum + 14}"
            elif exact and ssum <= 37:
                verdict = f"ALERT-{ssum + 14}"
            elif not exact and ssum > 37:
                verdict = "ruled-out-51"
            elif exact:
                verdict = f"total-{ssum + 14}"
            else:
                verdict = "undecided"
        else:
            ssum, verdict = "?", "timeout-unknown"
        iso = [x[1] for x in st]
        with open(RES, "a") as f:
            f.write(f"{stem},{floor},{iso[0]},{iso[1]},{iso[2]},"
                    f"{vals[0]},{vals[1]},{vals[2]},{ssum},{verdict},{secs:.0f}\n")
        print(f"{stem} floor={floor} iso={iso} legs={vals} -> {verdict}",
              flush=True)
        if str(verdict).startswith(("ALERT", "KLAXON")):
            print(f"*** {verdict}: {stem} ***", flush=True)
print("flipmint stopped.", flush=True)
