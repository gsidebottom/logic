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
import argparse, json, os, re, subprocess, tempfile, time, statistics as st


def _dimacs_vars(path):
    with open(path) as f:
        for ln in f:
            if ln.startswith("p cnf"):
                return int(ln.split()[2])
    return -1


def _phase_file_vars(path):
    """Var count from phase_infer's header 'c phase predictions: N vars, ...'."""
    with open(path) as f:
        head = f.readline()
    m = re.search(r"(\d+)\s+vars", head)
    return int(m.group(1)) if m else -1


def kissat(binary, cnf, phases=None, tcap=0):
    env = dict(os.environ)
    if phases:
        env["KISSAT_INITIAL_PHASES"] = phases
    cmd = [binary]
    if tcap:
        cmd.append(f"--time={tcap}")        # CPU-time cap → UNKNOWN if exceeded
    cmd.append(cnf)
    t0 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True, env=env)
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
    ap.add_argument("--infer", default=os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "phase_infer.py"),
        help="path to phase_infer.py (default: alongside this script, so it "
             "works regardless of the caller's cwd)")
    ap.add_argument("--time", type=int, default=0,
                    help="per-run kissat CPU-time cap (s); unfinished runs are "
                         "excluded from the aggregate, not counted as mismatches")
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
    n_skip = n_mismatch = n_used = n_inferfail = 0
    tmp = tempfile.mkdtemp(prefix="abk_")          # unique per process (no clobber)
    cnf_path, ph_path = os.path.join(tmp, "abk.cnf"), os.path.join(tmp, "abk.phases")
    for name, rec in items:
        subprocess.run(["sh", "-c", f"xz -dkc {rec['xz_path']} > {cnf_path}"], check=True)
        if os.path.exists(ph_path):
            os.remove(ph_path)                     # never reuse a stale phase file
        r = subprocess.run(["uv", "run", "python", args.infer, "--weights", args.weights,
                            "--cnf", cnf_path, "--out", ph_path,
                            "--margin", args.margin], capture_output=True, text=True)
        # Hard-fail loudly: a broken infer must NOT masquerade as a no-seed tie.
        if r.returncode != 0 or not os.path.exists(ph_path):
            print(f"{name[:30]:30} {'INFER-FAIL':>23}  rc={r.returncode} "
                  f"{(r.stderr or '').strip().splitlines()[-1][:50] if r.stderr else ''}")
            n_inferfail += 1
            continue
        cv, pv = _dimacs_vars(cnf_path), _phase_file_vars(ph_path)
        if cv != pv:
            print(f"{name[:30]:30} PHASE/CNF VAR MISMATCH {pv} vs {cv} — skip")
            n_inferfail += 1
            continue
        bv, bc, bts = kissat(args.kissat, cnf_path, tcap=args.time)
        wv, wc, wts = kissat(args.kissat, cnf_path, ph_path, tcap=args.time)
        # decided = both runs reached the SAME real verdict; only those count.
        decided = bv == wv and bv in ("SAT", "UNSAT")
        if not decided:
            both_solved = bv in ("SAT", "UNSAT") and wv in ("SAT", "UNSAT")
            if both_solved:
                tag = f"MISMATCH {bv}/{wv}"; n_mismatch += 1      # real soundness alarm
            else:
                tag = f"skip({bv}/{wv})"; n_skip += 1             # timeout/unknown
            ratio = float("nan")
        else:
            ratio = (wc / bc) if bc > 0 else float("nan")
            if bc > 0:
                ratios.append(ratio); bt += bts; wt += wts; n_used += 1
            tag = "ok"
        print(f"{name[:30]:30} {bc:>11} {wc:>11} {ratio:>6.2f}  "
              f"{bts:>7.2f} {wts:>7.2f}  {tag}")
    pos = [r for r in ratios if r > 0]
    print(f"\nusable={n_used}  skipped(timeout/trivial)={n_skip}  "
          f"infer_fail={n_inferfail}  mismatch={n_mismatch}")
    if pos:
        print(f"conflict ratio (warm/base): geomean={st.geometric_mean(pos):.3f}  "
              f"median={st.median(pos):.3f}  (<1 = warm-start helps)")
        print(f"total wall (usable only): base={bt:.1f}s  warm={wt:.1f}s "
              f"({100*(wt-bt)/bt:+.1f}%)")


if __name__ == "__main__":
    main()
