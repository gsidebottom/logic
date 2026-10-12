#!/usr/bin/env python3
"""Variant-aware supplemental KS sweep: fbsweep deduplicated targets by
(family, class NAME), but HKS names collide -- a -001.tab can be a
different de Groote class than its -000 sibling (S-P's third 51-class,
i12w219c23ci-008, was missed exactly this way).  This sweeper keys
everything by the exact tab member name, pre-seeds the done-set with
the first tgz occurrence of every (family, name) already decided by
the main sweep, and runs fbmin tiers on the remaining floor<=48 tabs.

Usage: fbsweep2.py schemes.tgz fbmin main_results.csv outdir
         [--threads T] [--max-floor N] [--leg-timeout S]
"""
import csv, pathlib, re, subprocess, sys, tarfile, time

args = sys.argv[1:]
flags = {"--threads": 2, "--max-floor": 48, "--leg-timeout": 2400}
pos = []
i = 0
while i < len(args):
    if args[i] in flags:
        flags[args[i]] = int(args[i + 1])
        i += 2
    else:
        pos.append(args[i])
        i += 1
TGZ, FBMIN, MAINCSV, OUTDIR = pos
OUT = pathlib.Path(OUTDIR)
OUT.mkdir(parents=True, exist_ok=True)
RES = OUT / "fbsweep2_results.csv"
STOP = OUT / "fbsweep2.STOP"
LEGS = OUT / "legs"
LEGS.mkdir(exist_ok=True)

main_done = set()
for r in csv.DictReader(open(MAINCSV)):
    main_done.add((r["family"], r["class"]))

done = set()
if RES.exists():
    for r in csv.DictReader(open(RES)):
        done.add(r["tab"])
else:
    RES.write_text("tab,family,class,floor2,legA,legB,legC,sum,verdict,secs\n")

def parse_tab(text):
    out, cur = [], []
    for ln in text.splitlines():
        if "|" not in ln:
            continue
        parts = [p.split() for p in ln.split("|")]
        if len(parts) != 3 or any(len(g) != 3 for g in parts):
            continue
        cur.append([[int(v) for v in g] for g in parts])
        if len(cur) == 3:
            out.append(tuple(tuple(v for r in cur for v in r[s]) for s in range(3)))
            cur = []
    return out

def d_of(rows):
    return len({r for r in rows if any(r)})

LEG_RE = re.compile(r"min_adds(>?=)(\d+) \[(.*?)\]")

def run_leg(path):
    try:
        out = subprocess.run(
            [FBMIN, "--tier3", "--threads", str(flags["--threads"]), str(path)],
            capture_output=True, text=True, timeout=flags["--leg-timeout"]).stdout
    except subprocess.TimeoutExpired:
        return ">=?"
    m = LEG_RE.search(out)
    return (("=" if m.group(1) == "=" else ">=") + m.group(2)) if m else ">=?"

tf = tarfile.open(TGZ, "r:gz")
first_seen = set()
targets = []
for m in tf:
    if not m.name.endswith(".tab"):
        continue
    fam = m.name.split("/")[1]
    cls = m.name.rsplit("/", 1)[-1].rsplit("-", 1)[0]
    key = (fam, cls)
    if key not in first_seen:
        first_seen.add(key)
        if key in main_done:
            continue          # the main sweep covered this exact tab
    targets.append(m.name)
print(f"supplemental targets (pre-floor-filter): {len(targets)}", flush=True)

for name in targets:
    tab = name.rsplit("/", 1)[-1]
    if tab in done:
        continue
    if STOP.exists():
        print("STOP file present -- halting.", flush=True)
        break
    fam = name.split("/")[1]
    cls = tab.rsplit("-", 1)[0]
    sm = parse_tab(tf.extractfile(name).read().decode())
    if len(sm) != 23:
        continue
    legs = [[("".join(str(v & 1) for v in t[s])) for t in sm] for s in range(3)]
    ds = [d_of([tuple(int(c) for c in r) for r in l]) for l in legs]
    floor = sum(ds) - 13
    if floor > flags["--max-floor"]:
        continue
    paths = []
    for l, nm in zip(legs, "ABC"):
        p = LEGS / f"{tab}_{nm}.legs"
        p.write_text("\n".join(l) + "\n")
        paths.append(p)
    t0 = time.time()
    vals = [run_leg(p) for p in paths]
    secs = time.time() - t0
    digs = [v.lstrip(">=") for v in vals]
    if not all(d.isdigit() for d in digs):
        verdict, s = "timeout-unknown", "?"
    else:
        nums = [int(d) for d in digs]
        s = sum(nums)
        exact = all(v.startswith("=") for v in vals)
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
    with open(RES, "a") as f:
        f.write(f"{tab},{fam},{cls},{floor},{vals[0]},{vals[1]},{vals[2]},{s},{verdict},{secs:.0f}\n")
    print(f"{tab} [{fam}] floor={floor} legs={vals} -> {verdict} ({secs:.0f} s)",
          flush=True)
    if str(verdict).startswith("ALERT"):
        print(f"*** ALERT: {tab} per-step {s + 14} ***", flush=True)
print("supplemental sweep pass complete.", flush=True)
