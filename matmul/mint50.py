#!/usr/bin/env python3
"""The 50-hunt minting loop (route 2 + light route 3): alternate
walk.py batches (pool-based scheme discovery, archive-deduped,
Brent-reverified) with the additive-structure screen and exact fbmin
tier evaluation.

Screen per leg: d (distinct rows), floor = sum d - 13 kept <= 48, plus
floor-49 schemes with >= 2 isolation-0 legs and floor-50 schemes with
all three (the only higher-floor shapes that can host a 50: slack is
50 - floor, and floor-achieving legs need isolation 0);
triple-isolated row count (rows in no internal addition triple) -- the
law says floor-achieving legs have isolation 0, and slack
grows ~isolated/2, so keepers are ranked by total isolation then
floor.  Exact evaluation: fbmin --tier3 per leg; ALERT at leg-sum <=
37 (per-step 51), klaxon at <= 36 (the 50).

Usage: mint50.py workdir anf fbmin [--threads T] [--batch-min M]
Stop: touch <workdir>/STOP.
"""
import pathlib, re, subprocess, sys, time

args = sys.argv[1:]
flags = {"--threads": 11, "--batch-min": 20}
pos = []
i = 0
while i < len(args):
    if args[i] in flags:
        flags[args[i]] = int(args[i + 1])
        i += 2
    else:
        pos.append(args[i])
        i += 1
WORK, ANF, FBMIN = (pathlib.Path(pos[0]), pos[1], pos[2])
ARCH = WORK / "archive"
LEGS = WORK / "legs"
RES = WORK / "mint_results.csv"
for d in (WORK, ARCH, LEGS):
    d.mkdir(parents=True, exist_ok=True)
if not RES.exists():
    RES.write_text("scheme,floor,isoA,isoB,isoC,legA,legB,legC,sum,verdict,secs\n")

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
    ws = sorted(r.count("1") for r in uniq)
    return len(uniq), len(ints) - len(in_tri), uniq, ws

def floor_legs(st, need):
    """True iff at least `need` legs attain their floor (exact,
    fbmin --tier1-only), stopping early either way."""
    import tempfile, os
    hits = misses = 0
    for (d_, i_, uniq, *_rest) in st:
        with tempfile.NamedTemporaryFile("w", suffix=".legs", delete=False) as f:
            f.write("\n".join(uniq) + "\n")
            path = f.name
        try:
            o = subprocess.run([FBMIN, "--tier1-only", "--threads", "1", path],
                               capture_output=True, text=True).stdout
        finally:
            os.unlink(path)
        if "tier1: 9-target basis closes" in o:
            hits += 1
        else:
            misses += 1
        if hits >= need:
            return True
        if misses > len(st) - need:
            return False
    return hits >= need


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
if RES.exists():
    for ln in RES.read_text().splitlines()[1:]:
        screened.add(ln.split(",")[0])

batch = 0
while not (WORK / "STOP").exists():
    batch += 1
    print(f"== mint batch {batch} ({flags['--batch-min']} min, "
          f"{flags['--threads']} threads) ==", flush=True)
    subprocess.run(
        [sys.executable, "walk.py", "--minutes", str(flags["--batch-min"]),
         "--threads", str(flags["--threads"]), "--seeds", str(WORK / "seeds"),
         "--archive", str(ARCH), "--anf", ANF],
        cwd=pathlib.Path(__file__).parent)
    news = []
    for p in sorted(ARCH.glob("*.bits")):
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
        # floor <= 48 as before; floor 49/50 can host a 50 only with
        # >= 2 / 3 legs attaining their floor d-9 (slack 50-floor),
        # decided exactly by fbmin --tier1-only (the earlier
        # isolation-0 shortcut was unsound: 5/32 floor legs have an
        # isolated row).  floor >= 51 is arithmetic.
        if floor > 50:
            continue
        if floor >= 49 and floor_legs(st, 2 if floor == 49 else 3) is False:
            continue
        news.append((sum(iso), floor, p.stem, st))
    news.sort()
    print(f"batch {batch}: {len(news)} floor<=48 keepers", flush=True)
    for toti, floor, stem, st in news:
        if (WORK / "STOP").exists():
            break
        paths = []
        for (d_, i_, uniq, _ws), nm in zip(st, "ABC"):
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
        print(f"{stem} floor={floor} iso={iso} legs={vals} -> {verdict}", flush=True)
        if str(verdict).startswith(("ALERT", "KLAXON")):
            print(f"*** {verdict}: {stem} ***", flush=True)
        if all(x.isdigit() for x in digs) and all(
                v.startswith("=") for v in vals):
            lbs = []
            for (d_, i_, uniq, ws), a in zip(st, (int(x) for x in digs)):
                k = max(9 - (a - (d_ - 9)), 0)
                lbs.append(sum(w - 1 for w in ws[:k]))
            oneshot_lb = sum(int(x) for x in digs) + 14 + sum(lbs)
            if oneshot_lb <= 55:
                print(f"*** LIGHT-{oneshot_lb}: {stem} one-shot bound "
                      f"{sum(int(x) for x in digs) + 14}+{sum(lbs)} "
                      f"<= 55 -- flat-record threat ***", flush=True)
print("mint50 stopped.", flush=True)
