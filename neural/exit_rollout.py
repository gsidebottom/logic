#!/usr/bin/env python3
"""
Expert-iteration rollout / headroom de-risk.

ExIt can only beat Phase-1 imitation if a *search* over seedings finds phases
that solve faster than v8's argmax (which merely imitates a satisfying witness).
For each instance we roll out several seedings and keep the best by CONFLICTS
(deterministic → parallelizable):

  - none      : no seed (solver default) — reference
  - argmax    : v8's mode (the current policy)
  - sample_k  : phases ~ Bernoulli(P(True)) at temperature T (explores the
                uncertain vars; high-confidence vars rarely flip)

Headroom = how much the best rollout beats argmax. If geomean(best/argmax) ≪ 1
on a meaningful fraction of instances, ExIt has fuel; if best ≈ argmax, phases
are tapped out (→ pivot to VSIDS-score seeding on cdcl.rs).

Usage: exit_rollout.py --weights neural/weights/phase_v8 --index <jsonl>
                       [--n 80 --samples 5 --temp 1.0 --time 20 --jobs 8]
"""
from __future__ import annotations
import argparse, json, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
import numpy as np
import mlx.core as mx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sat_graph                                       # noqa: E402
from phase_model import PhaseNet                       # noqa: E402

K = "/tmp/kissat-src/build/kissat"


def write_phases(path, lits, nv, ncl):
    with open(path, "w") as f:
        f.write(f"c {nv} vars {ncl} cls, {len(lits)} seeded\n")
        for i in range(0, len(lits), 20):
            f.write(" ".join(map(str, lits[i:i + 20])) + "\n")
        f.write("0\n")


def kissat_conflicts(cnf, phases, tcap):
    env = dict(os.environ)
    if phases:
        env["KISSAT_INITIAL_PHASES"] = phases
    p = subprocess.run([K, f"--time={tcap}", cnf], capture_output=True, text=True, env=env)
    solved = "s SATISFIABLE" in p.stdout or "s UNSATISFIABLE" in p.stdout
    c = -1
    for ln in p.stdout.splitlines():
        if ln.startswith("c conflicts:"):
            m = re.search(r"(\d+)", ln); c = int(m.group(1)) if m else -1
            break
    return solved, c


def rollout(rec, model, args):
    name = rec["filename"]
    if not os.path.exists(rec["xz_path"]):
        return None
    td = tempfile.mkdtemp(prefix="exit_")
    cnf = os.path.join(td, "c.cnf")
    subprocess.run(["sh", "-c", f"xz -dkc {rec['xz_path']} > {cnf}"], check=True)
    g = sat_graph.from_file(cnf)
    nv = g.n_vars
    inst = {"el": mx.array(g.edge_lit), "ec": mx.array(g.edge_clause),
            "flip": mx.array(g.flip), "n_lit": g.n_lit_nodes, "n_cls": g.n_clauses,
            "n_vars": nv, "pos": mx.arange(nv) * 2, "neg": mx.arange(nv) * 2 + 1}
    p = np.array(mx.sigmoid(model(inst)))               # P(True)

    def lits_of(phase_bool):
        return [((v + 1) if phase_bool[v] else -(v + 1)) for v in range(nv)]

    variants = {}
    variants["argmax"] = lits_of(p >= 0.5)
    rng = np.random.default_rng(abs(hash(name)) % (2**32))
    if args.uniform:
        pt = np.full(nv, 0.5)            # control: seeds independent of the policy
    else:
        pc = np.clip(p, 1e-4, 1 - 1e-4)
        pt = pc ** (1.0 / args.temp)
        pt = pt / (pt + (1 - pc) ** (1.0 / args.temp))
    for k in range(args.samples):
        variants[f"s{k}"] = lits_of(rng.random(nv) < pt)

    res = {"name": name, "n_vars": nv}
    # reference: no seed
    sv, sc = kissat_conflicts(cnf, None, args.time)
    res["none"] = sc if sv else None
    for tag, lits in variants.items():
        ph = os.path.join(td, f"{tag}.ph")
        write_phases(ph, lits, nv, g.n_clauses)
        sv, sc = kissat_conflicts(cnf, ph, args.time)
        res[tag] = sc if sv else None
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--weights", required=True)
    ap.add_argument("--index", required=True)
    ap.add_argument("--n", type=int, default=80)
    ap.add_argument("--samples", type=int, default=5)
    ap.add_argument("--temp", type=float, default=1.0)
    ap.add_argument("--uniform", action="store_true",
                    help="CONTROL: sample seeds uniformly (0.5), policy-independent "
                         "— if best-of-K still beats argmax, the headroom is "
                         "seed-variance/portfolio, not learnable policy signal")
    ap.add_argument("--time", type=int, default=20)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--out", default="/tmp/exit_rollout.json")
    args = ap.parse_args()
    mx.set_default_device(mx.cpu)

    base = args.weights
    cfg = json.load(open(base + ".json"))
    model = PhaseNet(cfg["dim"], cfg["rounds"]); model.load_weights(base + ".safetensors")
    mx.eval(model.parameters())

    recs = [json.loads(l) for l in open(args.index)][:args.n]
    print(f"rollout: {len(recs)} instances, {args.samples} samples (T={args.temp}), "
          f"cap {args.time}s")
    rows = []
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for i, r in enumerate(ex.map(lambda rr: rollout(rr, model, args), recs), 1):
            if r:
                rows.append(r)
            if i % 20 == 0:
                print(f"  {i}/{len(recs)}")
    json.dump(rows, open(args.out, "w"))

    # analysis: only instances where argmax solved within the cap
    sk = [f"s{k}" for k in range(args.samples)]
    usable = [r for r in rows if r.get("argmax")]
    print(f"\nusable (argmax solved in {args.time}s): {len(usable)}/{len(rows)}")
    g_ba, g_bn, g_an = [], [], []
    win_sample = 0
    for r in usable:
        am = r["argmax"]
        samp = [r[k] for k in sk if r.get(k)]
        best = min([am] + samp)                          # best of argmax+samples
        if best < am:
            win_sample += 1
        g_ba.append(best / am)
        if r.get("none"):
            g_an.append(am / r["none"]); g_bn.append(best / r["none"])

    def gm(x):
        x = [v for v in x if v and v > 0]
        return float(np.exp(np.mean(np.log(x)))) if x else float("nan")
    print(f"\nHEADROOM (the ExIt question):")
    print(f"  geomean best/argmax   = {gm(g_ba):.3f}   "
          f"(<1 ⇒ a sampled seed beats the v8 policy → ExIt has fuel)")
    print(f"  instances where a sample beats argmax: {win_sample}/{len(usable)} "
          f"({100*win_sample/max(1,len(usable)):.0f}%)")
    print(f"  recap geomean argmax/none = {gm(g_an):.3f}  (v8 policy vs no-seed)")
    print(f"  geomean best/none         = {gm(g_bn):.3f}  (ExIt ceiling vs no-seed)")


if __name__ == "__main__":
    main()
