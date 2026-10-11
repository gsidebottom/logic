#!/usr/bin/env python3
"""Standing background sweep for the KS-model 51 hunt: run fbmin
(exact free-basis leg minimization, tiers 1-3) over DB classes in
rising-floor order, 2 threads, one class at a time.

A class reaches per-step total <= 51 iff its three leg minima sum to
<= 37 (output leg = C-leg + 14).  Leg minima are de Groote class
invariants, so one representative per (family, class) suffices.

Inputs: dprofile.csv (from dprofile.py), dbcache/schemes.tgz, the
fbmin binary.  Outputs: results CSV (one row per class, resumable),
log lines with ALERT on any sum <= 37 (51!) or == 38 (52 tie).
Controls: touch <outdir>/fbsweep.STOP to halt after the current class;
per-leg subprocess timeout (default 1800 s) keeps tier-3 exhaustions
bounded.

Usage: fbsweep.py dprofile.csv schemes.tgz fbmin-binary outdir
         [--max-floor N] [--threads T] [--leg-timeout S]
"""
import csv, pathlib, re, subprocess, sys, tarfile, time

args = sys.argv[1:]
flags = {"--max-floor": 48, "--threads": 2, "--leg-timeout": 1800}
pos = []
i = 0
while i < len(args):
    if args[i] in flags:
        flags[args[i]] = int(args[i + 1])
        i += 2
    else:
        pos.append(args[i])
        i += 1
CSV, TGZ, FBMIN, OUTDIR = pos
OUT = pathlib.Path(OUTDIR)
OUT.mkdir(parents=True, exist_ok=True)
RES = OUT / "fbsweep_results.csv"
STOP = OUT / "fbsweep.STOP"
LEGS = OUT / "legs"
LEGS.mkdir(exist_ok=True)

DONE_ALREADY = {"i19w225c4efh", "i12w195c23ci"}  # settled 2026-10-10: both 52

# ---- target list: dedup by (family, class), sort by floor then sharing
rows = list(csv.DictReader(open(CSV)))
seen, targets = set(), []
for r in rows:
    key = (r["family"], r["class"])
    if key in seen or r["class"] in DONE_ALREADY:
        continue
    seen.add(key)
    f2 = int(r["floor2"])
    if f2 > flags["--max-floor"]:
        continue
    dmin = min(int(r["dA2"]), int(r["dB2"]), int(r["dC2"]))
    targets.append((f2, dmin, r["family"], r["class"]))
targets.sort()
print(f"sweep targets: {len(targets)} classes (floor <= {flags['--max-floor']})", flush=True)

done = set()
if RES.exists():
    for r in csv.DictReader(open(RES)):
        done.add((r["family"], r["class"]))
else:
    RES.write_text("family,class,floor2,legA,legB,legC,sum,verdict,secs\n")

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

def emit_legs(tf, family, cls):
    name = f"schemes/{family}/{cls}-000.tab"
    try:
        m = tf.getmember(name)
    except KeyError:
        for m2 in tf.getmembers():
            if m2.name.startswith(f"schemes/{family}/{cls}-") and m2.name.endswith(".tab"):
                m = m2
                break
        else:
            return None
    sm = parse_tab(tf.extractfile(m).read().decode())
    if len(sm) != 23:
        return None
    paths = []
    for side, nm in enumerate("ABC"):
        p = LEGS / f"{family.replace('/', '_')}__{cls}_{nm}.legs"
        p.write_text("\n".join("".join(str(v & 1) for v in t[side]) for t in sm) + "\n")
        paths.append(p)
    return paths

LEG_RE = re.compile(r"min_adds(>?=)(\d+) \[(.*?)\]")

def run_leg(path):
    t0 = time.time()
    try:
        out = subprocess.run(
            [FBMIN, "--tier3", "--threads", str(flags["--threads"]), str(path)],
            capture_output=True, text=True, timeout=flags["--leg-timeout"],
        ).stdout
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        m = LEG_RE.search(out)
        if m:
            return (f">={m.group(2)}", time.time() - t0, "timeout")
        return (">=?", time.time() - t0, "timeout")
    m = LEG_RE.search(out)
    if not m:
        return ("parse-error", time.time() - t0, out[:120])
    op, val, how = m.groups()
    assert "CERT-OK" in out or op == ">=", "positive result without certificate"
    return (("=" if op == "=" else ">=") + val, time.time() - t0, how)

tf = tarfile.open(TGZ, "r:gz")
for f2, dmin, family, cls in targets:
    if (family, cls) in done:
        continue
    if STOP.exists():
        print("STOP file present -- halting.", flush=True)
        break
    paths = emit_legs(tf, family, cls)
    if paths is None:
        with open(RES, "a") as f:
            f.write(f"{family},{cls},{f2},?,?,?,?,extract-failed,0\n")
        continue
    t0 = time.time()
    legs = [run_leg(p) for p in paths]
    secs = time.time() - t0
    vals = [v for v, _, _ in legs]
    digs = [v.lstrip(">=") for v in vals]
    if not all(d.isdigit() for d in digs):
        # a killed/unparsable fbmin run (e.g. timeout): record and move on
        with open(RES, "a") as f:
            f.write(f"{family},{cls},{f2},{vals[0]},{vals[1]},{vals[2]},?,"
                    f"timeout-unknown,{secs:.0f}\n")
        print(f"{cls} [{family}] leg unparsable -> timeout-unknown", flush=True)
        continue
    exact = all(v.startswith("=") for v in vals)
    nums = [int(d) for d in digs]
    s = sum(nums)
    if exact and s <= 37:
        verdict = f"ALERT-{s + 14}"
    elif exact and s == 38:
        verdict = "tie-52"
    elif not exact and s > 37:
        verdict = "ruled-out-51"
    elif not exact:
        verdict = "undecided"
    else:
        verdict = f"total-{s + 14}"
    with open(RES, "a") as f:
        f.write(f"{family},{cls},{f2},{vals[0]},{vals[1]},{vals[2]},{s},{verdict},{secs:.0f}\n")
    print(f"{cls} [{family}] floor={f2} legs={vals} sum{'=' if exact else '>='}"
          f"{s} -> {verdict} ({secs:.0f} s)", flush=True)
    if verdict.startswith("ALERT"):
        print(f"*** ALERT: {cls} reaches per-step total {s + 14} <= 51 ***", flush=True)
print("sweep pass complete.", flush=True)
