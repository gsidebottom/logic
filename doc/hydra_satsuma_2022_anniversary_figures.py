#!/usr/bin/env python3
"""The numbers and figures of doc/hydra_satsuma_2022_anniversary_results.tex:
the SC2022 anniversary duo run (satsuma vs hydra_circuit_satsuma) decomposed
stage by stage into what each stage won and what it cost, in seconds of the
PAR-2 sum, plus the comparison with the 2022 field under the measured speed
factor.

    doc/hydra_satsuma_2022_anniversary_figures.py            # prints the tables
    doc/hydra_satsuma_2022_anniversary_figures.py --figures  # also writes the PDFs

Reads the run directory (results, logs, stage scan, symmetry probe) and the
SC2022 detailed results; writes doc/hydra_satsuma_2022_anniversary_*.pdf.
"""
import collections
import csv
import json
import math
import re
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
B = Path("/Users/greg/projects/sat_benchmarks")
RUN = B / "runs" / "anni_2022_duo"
T = 5000.0
OK = ("SAT", "UNSAT")

cfg = json.load(open(RUN / "config.json"))
order = cfg["order"]
recs = cfg["records"]
pos = {h: i + 1 for i, h in enumerate(order)}
res = {}
for line in open(RUN / "results.jsonl"):
    r = json.loads(line)
    res[(r["hash"], r["backend"])] = r
scan = {}
for line in open(RUN / "stage_scan.jsonl"):
    s = json.loads(line)
    scan[s["hash"]] = s
probe = {}
for line in open(RUN / "sym_probe.jsonl"):
    p = json.loads(line)
    probe[p["hash"]] = p
ref = {r["hash"]: r for r in csv.DictReader(open(B / "sc2022" / "anni-seq.csv"))}
SOLVERS = [k for k in next(iter(ref.values())) if k not in ("hash", "benchmark", "verified-result", "claimed-result")]

RX = {
    "factoring": re.compile(r"factoring stage: .*?\(.*?([0-9.]+)ms\)"),
    "xor": re.compile(r"xor stage: .*?\(([0-9.]+)ms\)"),
    "xor_ignored": re.compile(r"GE-forced — ignored in certified mode \(([0-9.]+)ms\)"),
    "circuit": re.compile(r"circuit stage: \d+ gates in \d+ clauses; factoring finds .*?\(([0-9.]+)s\)"),
    "cook": re.compile(r"Cook shape .*? in ([0-9.]+)ms"),
    "handoff": re.compile(r"engine hand-off at ([0-9.]+)ms"),
}


def par(r):
    return r["time_s"] if r["result"] in OK else 2 * T


def stage_of(h):
    o = scan[h]["outcome"]
    return o.split()[-1] if o.startswith("decided") else None


rows = []
for h in order:
    a, b = res[(h, "satsuma")], res[(h, "hydra_circuit_satsuma")]
    log = (RUN / "logs" / f"{h}.hydra_circuit_satsuma.err").read_text(errors="replace")
    t = {k: 0.0 for k in RX}
    for k, rx in RX.items():
        m = rx.search(log)
        if m:
            t[k] = float(m.group(1)) / (1.0 if k == "circuit" else 1000.0)
    rows.append(dict(h=h, name=recs[h]["name"], family=recs[h].get("family", "?"), nvars=recs[h].get("nvars") or 0,
                     nclauses=recs[h].get("nclauses") or 0, sat=a, hcs=b, reused=b.get("reused_from") is not None,
                     stage=stage_of(h), d=par(a) - par(b), **{f"t_{k}": v for k, v in t.items()}))

N = len(rows)
gap = sum(r["d"] for r in rows)
ps = sum(par(r["sat"]) for r in rows) / N
ph = sum(par(r["hcs"]) for r in rows) / N
print(f"instances {N}; PAR-2 satsuma {ps:.1f}, hydra_circuit_satsuma {ph:.1f}, gap {ps - ph:.2f} = {gap:.0f} s")

# ---- benefits
uniq = [r for r in rows if (r["sat"]["result"] in OK) != (r["hcs"]["result"] in OK)]
decided = [r for r in rows if r["stage"]]
speed = [r for r in decided if r not in uniq]
full = [r for r in rows if not r["reused"] and not r["stage"]]
hand = [r for r in rows if r["reused"]]
print(f"unique {len(uniq)}, stage-decided speed wins {len(speed)}, hand-offs {len(hand)}, full-run pairs {len(full)}")
by_stage_u = collections.Counter(r["stage"] for r in uniq)
by_stage_s = collections.defaultdict(float)
by_stage_n = collections.Counter()
for r in speed:
    by_stage_s[r["stage"]] += r["d"]
    by_stage_n[r["stage"]] += 1
print("benefits by stage (s of PAR-2 sum):")
for st in ("xor", "cook", "factoring"):
    u = [r for r in uniq if r["stage"] == st]
    print(f"  {st:9s} unique {len(u)} = {sum(r['d'] for r in u):8.0f} s; speed wins on {by_stage_n[st]} = {by_stage_s[st]:8.0f} s "
          f"(median satsuma time {statistics.median([r['sat']['time_s'] for r in speed if r['stage'] == st]) if by_stage_n[st] else 0:.2f} s)")

# ---- costs on hand-offs, by stage
cost = {k: sum(r[f"t_{k}"] for r in hand) for k in ("factoring", "xor", "xor_ignored", "circuit", "cook")}
handoff = sum(r["t_handoff"] for r in hand)
other = handoff - cost["factoring"] - cost["xor"] - cost["circuit"]
print(f"hand-off prefix total {handoff:.0f} s over {len(hand)} instances (mean {handoff / len(hand):.3f} s): "
      f"factoring {cost['factoring']:.0f}, xor {cost['xor']:.0f} (of which discarded propagation {cost['xor_ignored']:.0f}), "
      f"circuit trial {cost['circuit']:.0f}, other {other:.0f}")
prefix_charged = sum(r["hcs"].get("prefix_s") or 0 for r in hand)
print(f"  charged prefix (results.jsonl prefix_s) {prefix_charged:.0f} s")
full_d = sum(r["d"] for r in full)
print(f"full-run pairs: net {full_d:.0f} s (noise; {sum(1 for r in full if r['d'] > 0)} favour hcs, {sum(1 for r in full if r['d'] < 0)} satsuma)")
print(f"check: uniques {sum(r['d'] for r in uniq):.0f} + speed {sum(r['d'] for r in speed):.0f} + hand-offs {sum(r['d'] for r in hand):.0f} + full {full_d:.0f} = {sum(r['d'] for r in uniq) + sum(r['d'] for r in speed) + sum(r['d'] for r in hand) + full_d:.0f}")

# largest circuit trials and xor costs
print("largest circuit trials:", [(r["name"][:28], round(r["t_circuit"], 1)) for r in sorted(hand, key=lambda r: -r["t_circuit"])[:6]])
print("largest xor costs:", [(r["name"][:28], round(r["t_xor"], 1)) for r in sorted(hand, key=lambda r: -r["t_xor"])[:6]])
print("hand-offs with prefix > 10 s:", sum(1 for r in hand if r["t_handoff"] > 10), "> 1 s:", sum(1 for r in hand if r["t_handoff"] > 1))

# ---- the symmetry probe, final calibration
def klass(p):
    if not p or "dejavu_gens" not in p:
        return "no probe"
    if p.get("empty"):
        return "refuted"
    if p["dejavu_gens"] == 0:
        return "none"
    if sum(p.get(k, 0) for k in ("symmetry_units", "symmetry_binary", "symmetry_lex", "row", "row_column", "johnson")):
        return "breaks"
    return "found"
print("symmetry probe classes vs satsuma's final result on the 264 stage-decided instances:")
for k in ("refuted", "breaks", "none"):
    hs = [r for r in decided if klass(probe.get(r["h"])) == k]
    ok = sorted(r["sat"]["time_s"] for r in hs if r["sat"]["result"] in OK)
    fail = [r["name"][:24] for r in hs if r["sat"]["result"] not in OK]
    print(f"  {k:8s} n={len(hs):3d} satsuma solved {len(ok):3d} median {statistics.median(ok) if ok else 0:.2f} s max {ok[-1] if ok else 0:.1f} s; failed: {fail}")

# ---- the 2022 field, with the speed factor
def field_times(h):
    return [float(ref[h][s]) for s in SOLVERS]
vbs = {r["h"]: min(field_times(r["h"])) for r in rows}
win = {r["h"]: float(ref[r["h"]]["Kissat_MAB_ESA"]) for r in rows}
bulky = {r["h"]: float(ref[r["h"]]["kissat-sc2022-bulky"]) for r in rows}
def score(times, k=1.0):
    n = sum(1 for t in times if t is not None and k * t < T)
    p = sum((k * t if (t is not None and k * t < T) else 2 * T) for t in times) / len(times)
    return n, p
def ours(b):
    return [res[(r["h"], b)]["time_s"] if res[(r["h"], b)]["result"] in OK else None for r in rows]
print("2022 field on all 5,355: VBS", score([t if t < T else None for t in vbs.values()]), "winner", score([t if t < T else None for t in win.values()]),
      "bulky", score([t if t < T else None for t in bulky.values()]))
for k in (1, 2, 3, 4, 5, 6):
    print(f"  k={k}: satsuma {score(ours('satsuma'), k)}  hcs {score(ours('hydra_circuit_satsuma'), k)}")
for b in ("satsuma", "hydra_circuit_satsuma"):
    ts = ours(b)
    ks = [x / 100 for x in range(100, 1201)]
    wn, wp = score([t if t < T else None for t in win.values()])
    vn, vp = score([t if t < T else None for t in vbs.values()])
    print(f"  {b}: beats the winner's count while k <= {max(k for k in ks if score(ts, k)[0] > wn)}, its PAR-2 while k <= {max(k for k in ks if score(ts, k)[1] < wp)}; "
          f"beats the VBS count while k <= {max((k for k in ks if score(ts, k)[0] > vn), default=0)}")
beyond = {b: sum(1 for r in rows if res[(r["h"], b)]["result"] in OK and vbs[r["h"]] >= T) for b in ("satsuma", "hydra_circuit_satsuma")}
missed = {b: sum(1 for r in rows if res[(r["h"], b)]["result"] not in OK and vbs[r["h"]] < T) for b in ("satsuma", "hydra_circuit_satsuma")}
print("solved here and by none of 2022:", beyond, "| solved by 2022's VBS and not here:", missed)

# ---- by family: where the gap comes from
fam = collections.defaultdict(lambda: [0, 0.0, 0, 0])
for r in rows:
    f = fam[r["family"]]
    f[0] += 1; f[1] += r["d"]; f[2] += r["sat"]["result"] in OK; f[3] += r["hcs"]["result"] in OK
top = sorted(fam.items(), key=lambda kv: -abs(kv[1][1]))[:12]
print("families by |contribution| (n, s of gap, solved satsuma, solved hcs):")
for k, v in top:
    print(f"  {k:28s} {v[0]:4d} {v[1]:9.0f} {v[2]:4d} {v[3]:4d}")

if "--figures" in sys.argv:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    # cactus: ours and the 2022 field's best entrants
    fig, ax = plt.subplots(figsize=(6.4, 4.0))
    def cactus(times, label, **kw):
        ts = sorted(t for t in times if t is not None and t < T)
        ax.plot(ts, range(1, len(ts) + 1), label=f"{label} ({len(ts)})", **kw)
    cactus(ours("hydra_circuit_satsuma"), "hydra_circuit_satsuma", color="C3", lw=1.6)
    cactus(ours("satsuma"), "satsuma", color="C0", lw=1.6)
    cactus([t if t < T else None for t in vbs.values()], "2022 virtual best", color="0.3", lw=1.2, ls="--")
    cactus([t if t < T else None for t in bulky.values()], "kissat-sc2022-bulky", color="0.55", lw=1.0, ls=":")
    cactus([t if t < T else None for t in win.values()], "Kissat_MAB_ESA", color="0.7", lw=1.0, ls="-.")
    ax.set_xscale("log"); ax.set_xlim(1, T); ax.set_ylim(2500, 4500)
    ax.set_xlabel("time per instance (s); ours is wall-clock on the Apple M4 Pro, 2022's is CPU time on StarExec", fontsize=8.5)
    ax.set_ylabel("instances solved within the time")
    ax.grid(alpha=0.3); ax.legend(loc="upper left", fontsize=8)
    fig.tight_layout(); fig.savefig(ROOT / "doc" / "hydra_satsuma_2022_anniversary_cactus.pdf"); plt.close(fig)
    # contributions bar chart
    fig, ax = plt.subplots(figsize=(6.4, 3.2))
    items = [("XOR stage: 6 unique wins", sum(r["d"] for r in uniq if r["stage"] == "xor")),
             ("Cook prover: 2 unique wins", sum(r["d"] for r in uniq if r["stage"] == "cook")),
             ("XOR stage: speed wins", by_stage_s["xor"]), ("Cook prover: speed wins", by_stage_s["cook"]),
             ("factoring stage: speed wins", by_stage_s["factoring"]),
             ("full-run pairs (noise)", full_d),
             ("factoring trial on hand-offs", -cost["factoring"]), ("XOR stage on hand-offs", -cost["xor"]),
             ("circuit trial on hand-offs", -cost["circuit"]), ("other prefix on hand-offs", -other)]
    labels = [i[0] for i in items][::-1]; vals = [i[1] / N for i in items][::-1]
    ax.barh(labels, vals, color=["C3" if v < 0 else "C2" for v in vals])
    for y, v in enumerate(vals):
        ax.text(max(v, 0) + 0.15, y, f"{v:+.2f}", va="center", ha="left", fontsize=8)
    ax.axvline(0, color="k", lw=0.8)
    ax.set_xlabel("PAR-2 points over the 5,355 instances\n(positive favours hydra_circuit_satsuma)", fontsize=8.5)
    ax.set_xlim(min(vals) * 1.3 - 0.2, max(vals) * 1.2 + 0.3)
    fig.tight_layout(); fig.savefig(ROOT / "doc" / "hydra_satsuma_2022_anniversary_contributions.pdf"); plt.close(fig)
    print("figures written")
