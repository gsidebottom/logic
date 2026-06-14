#!/usr/bin/env python3
"""
§4b A/B — kissat baseline vs neural phase warm-start.

Runs the patched kissat (neural/kissat/neural_phase_warmstart.patch — seeds
`kissat_decide_phase` from $KISSAT_INITIAL_PHASES) with vs without a predicted
phase file, on HELD-OUT instances. kissat is deterministic, so single runs are
clean. Metric: conflicts + wall time; verdicts must match (soundness).

Usage:
  ab_kissat.py --kissat <patched-kissat> --weights neural/weights/phase_v2 \
               --margin 0.6 --index <jsonl with xz_path> [--split-from <manifest>]
"""
from __future__ import annotations
import argparse, json, os, re, subprocess, time, statistics as st


def kissat(binary, cnf, phases=None):
    env = dict(os.environ)
    if phases:
        env["KISSAT_INITIAL_PHASES"] = phases
    t0 = time.time()
    p = subprocess.run([binary, cnf], capture_output=True, text=True, env=env)
    dt = time.time() - t0
    out = p.stdout
    v = ("SAT" if "s SATISFIABLE" in out
         else "UNSAT" if "s UNSATISFIABLE" in out else "?")
    conf = -1
    for ln in out.splitlines():
        if ln.startswith("c conflicts:"):
            m = re.search(r"(\d+)", ln); conf = int(m.group(1)) if m else -1
            break
    return v, conf, dt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kissat", required=True, help="patched kissat binary")
    ap.add_argument("--weights", required=True, help="phase predictor base path")
    ap.add_argument("--margin", default="0.6")
    ap.add_argument("--index", required=True, help="jsonl with filename + xz_path")
    ap.add_argument("--split-from", help="manifest.jsonl: only its split==test rows")
    ap.add_argument("--infer", default="neural/phase_infer.py")
    args = ap.parse_args()

    idx = {json.loads(l)["filename"]: json.loads(l) for l in open(args.index)}
    if args.split_from:
        names = {e["filename"] for e in (json.loads(l) for l in open(args.split_from))
                 if e.get("split") == "test" and e.get("sat") == 1}
        items = [(n, idx[n]) for n in names if n in idx]
    else:
        items = list(idx.items())
    items = [(n, r) for n, r in items if r.get("xz_path") and os.path.exists(r["xz_path"])]

    print(f"kissat A/B ({os.path.basename(args.weights)} @ margin {args.margin}), "
          f"{len(items)} instances")
    print(f"{'instance':28} {'base':>11} {'warm':>11} {'ratio':>6}  "
          f"{'base_s':>7} {'warm_s':>7}  verdict")
    ratios, bt, wt = [], 0.0, 0.0
    for name, rec in items:
        subprocess.run(["sh", "-c", f"xz -dkc {rec['xz_path']} > /tmp/abk.cnf"], check=True)
        subprocess.run(["uv", "run", "python", args.infer, "--weights", args.weights,
                        "--cnf", "/tmp/abk.cnf", "--out", "/tmp/abk.phases",
                        "--margin", args.margin], capture_output=True)
        bv, bc, bts = kissat(args.kissat, "/tmp/abk.cnf")
        wv, wc, wts = kissat(args.kissat, "/tmp/abk.cnf", "/tmp/abk.phases")
        ok = "ok" if bv == wv and bv in ("SAT", "UNSAT") else f"MISMATCH {bv}/{wv}"
        ratio = (wc / bc) if bc > 0 else float("nan")
        if bc > 0:
            ratios.append(ratio)
        bt += bts; wt += wts
        print(f"{name[:28]:28} {bc:>11} {wc:>11} {ratio:>6.2f}  "
              f"{bts:>7.2f} {wts:>7.2f}  {ok}")
    pos = [r for r in ratios if r > 0]
    print(f"\nconflict ratio (warm/base): geomean={st.geometric_mean(pos):.3f}  "
          f"median={st.median(ratios):.3f}  (<1 = warm-start helps)")
    print(f"total wall: base={bt:.1f}s  warm={wt:.1f}s")


if __name__ == "__main__":
    main()
