#!/usr/bin/env python3
"""The results table and the cactus figure of doc/hydra_satsuma_solver.tex.

Scores every arm the way the paper's table does: all 400 official benchmarks
(duplicate hashes count twice), an UNSAT certified when its proof verified in
the main run or in the official-budget re-check runs, PAR-2 = solve time for
SAT and certified UNSAT, 2 x 5000 s otherwise.  Then draws the four-arm
cactus (solve time on x, cumulative solved on y, a dot per benchmark).

    doc/hydra_satsuma_solver_figures.py            # prints the table
    doc/hydra_satsuma_solver_figures.py --cactus   # also rewrites doc/hydra_satsuma_solver_cactus.pdf
"""
import json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IDX = Path("/Users/greg/projects/sat_benchmarks/main_track_2026_official.jsonl")
D = ROOT / "doc"

def rows(p):
    d = json.load(open(p)); return d["results"] if isinstance(d, dict) else d

def by_hash(p):
    out = {}
    for r in rows(p):
        out.setdefault(r["hash"], r)
    return out

index = [json.loads(l) for l in open(IDX) if l.strip()]
assert len(index) == 400

recheck = {}
for f in ("competition-benchmark_unchecked26_5000_hydra_satsuma.json",
          "competition-benchmark_mchess17_5000_satsuma.json",
          "competition-benchmark_hydra_memout2_5000_hydra_2.json"):
    for h, r in by_hash(D / f).items():
        if r.get("pb_proof_ok") is True:
            recheck[h] = r

ARMS = {
    "hydra": "competition-benchmark_main_track_2026_official_5000_hydra.json",
    "satsuma": "competition-benchmark_main_track_2026_official_5000_satsuma.json",
    "hydra_satsuma": "competition-benchmark_main_track_2026_official_5000_hydra_satsuma_2.json",
    # the 2026-10-01/02 run (memory-aware scheduling, 32 GB VM); the 09-30 run is the file without _2
    "hydra_circuit_satsuma": "competition-benchmark_main_track_2026_official_5000_hydra_circuit_satsuma_2.json",
}

def score(arm, path, timeout=5000):
    res = by_hash(path)
    sat = unsat = cert = 0; par = 0.0; uncert = []
    for row in index:
        r = res.get(row["hash"])
        if r is None:
            raise SystemExit(f"{arm}: no result for {row['filename']}")
        v = r.get("result")
        if v == "SAT":
            sat += 1; par += r["time_s"]
        elif v == "UNSAT":
            unsat += 1
            ok = r.get("pb_proof_ok") is True or row["hash"] in recheck
            if ok: cert += 1; par += r["time_s"]
            else: par += 2 * timeout; uncert.append(row["filename"].replace(".cnf.xz", ""))
        else:
            par += 2 * timeout
    return dict(solved=sat + unsat, sat=sat, unsat=unsat, certified=cert, par2=par / 400, uncertified=uncert)


def table():
    print(f"{'arm':22s} {'solved':>6s} {'SAT':>4s} {'UNSAT':>5s} {'cert':>5s} {'PAR-2':>8s}  uncertified UNSATs")
    for arm, f in ARMS.items():
        s = score(arm, D / f)
        print(f"{arm:22s} {s['solved']:6d} {s['sat']:4d} {s['unsat']:5d} {s['certified']:5d} {s['par2']:8.2f}  {', '.join(s['uncertified'])}")

def cactus(out):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    def curve(path):
        res = by_hash(D / path)
        ts = sorted(r["time_s"] for row in index for r in [res[row["hash"]]] if r.get("result") in ("SAT", "UNSAT"))
        return ts, list(range(1, len(ts) + 1))
    style = {
        "hydra": dict(color="#3a6fd8", lw=0.9, zorder=3, ms=2.0),
        "satsuma": dict(color="#2fb37a", lw=5.0, alpha=0.45, zorder=1, ms=0),
        "hydra_satsuma": dict(color="#b5651d", lw=0.9, zorder=4, ms=2.0),
        "hydra_circuit_satsuma": dict(color="#8e2bb5", lw=0.9, zorder=5, ms=2.0),
    }
    fig, ax = plt.subplots(figsize=(6.4, 3.9), dpi=150)
    for arm, path in ARMS.items():
        ts, ns = curve(path); st = style[arm]
        ax.plot(ts, ns, "-", color=st["color"], lw=st["lw"], alpha=st.get("alpha", 1.0), zorder=st["zorder"],
                label=f"{arm} ({len(ts)} solved)")
        if st["ms"]:
            ax.plot(ts, ns, "o", color=st["color"], ms=st["ms"], mew=0, alpha=0.6, zorder=st["zorder"])
    ax.axvline(5000, color="#999", lw=0.8, ls="--", zorder=0)
    ax.text(5000, 40, "5000 s timeout", rotation=90, color="#888", fontsize=7, ha="right", va="bottom")
    ax.set_xlim(0, 5150); ax.set_ylim(0, 400)
    ax.set_xlabel("solve time per instance (s, wall)", fontsize=9)
    ax.set_ylabel("solved instances (cumulative)", fontsize=9)
    ax.tick_params(labelsize=8)
    ax.grid(True, color="#e5e5e5", lw=0.6)
    for s in ("top", "right"): ax.spines[s].set_visible(False)
    leg = ax.legend(loc="lower right", fontsize=8, frameon=False)
    for h in leg.get_lines(): h.set_linewidth(max(h.get_linewidth(), 2.0))
    fig.tight_layout()
    fig.savefig(out)
    print("wrote", out)

if __name__ == "__main__":
    table()
    if "--cactus" in sys.argv:
        cactus(D / "hydra_satsuma_solver_cactus.pdf")
