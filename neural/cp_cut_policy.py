#!/usr/bin/env python3
"""
Cut-selection policy for the LP-CG engine (Phase 3, step C+).

The brute-force loop (`cp_lp.cg_loop`) separates everything and adds every
violated cut — it refutes PHP-3-2/4-3 but explodes on PHP-5-4, because the
constraint set grows every round and the separation MILPs slow down with it. Yet
most added cuts are WASTED: only the few in the final Farkas refutation actually
matter. A learned scorer that keeps the system small by adding only the useful
cuts should reach infeasibility with far fewer cuts and scale further.

Imitation: run the brute-force loop on instances it solves; trace the final Farkas
support *backward through the cut derivations* to label each added cut useful/not;
fit a logistic scorer over cheap cut features; then re-run adding only the
top-scored cuts and compare cut counts / solve time. The headline test is
TRANSFER — a scorer trained on small PHP making PHP-5-4 tractable.

Usage: cp_cut_policy.py [--train 3_2 4_3] [--eval 4_3 5_4] [--topfrac 0.4]
"""
from __future__ import annotations
import argparse, os, sys, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cp_search as cp
import cp_lp
from cp_policy import logreg_fit, standardize


FEAT_NAMES = ["viol", "q", "nsrc", "msum", "degree", "ncoef", "maxc", "sumc",
              "density"]


def cnf_path(tag):
    return f"/tmp/php_{tag}/php_{tag}.cnf"


def cut_feats(viol, mults, q, cut, nvars):
    """Cheap intrinsic features of a candidate cut (no engine state needed)."""
    coefs = [abs(a) for a in cut.coef.values()]
    return [float(viol), float(q), float(len(mults)),
            float(sum(mults.values())), float(abs(cut.rhs)),
            float(len(cut.coef)), float(max(coefs) if coefs else 0),
            float(sum(coefs)), len(cut.coef) / max(1, nvars)]


def compute_useful(n_inputs, cut_derivs, mult):
    """Cons-indices in the TRANSITIVE support of the final Farkas refutation: a
    constraint with nonzero multiplier is useful, and so is every constraint that
    a useful CUT was derived from (walk cut_derivs backward)."""
    useful = {j for j in range(len(mult)) if abs(mult[j]) > 1e-9}
    for k in range(len(cut_derivs) - 1, -1, -1):          # cut k lives at n_inputs+k
        if (n_inputs + k) in useful:
            useful.update(cut_derivs[k][0])               # its source cons-indices
    return useful


def _rounds(inputs, nvars, qmax, n_obj, max_rounds, seed, scorer=None,
            topfrac=1.0, max_secs=600):
    """Shared LP-CG loop.  scorer=None ⇒ brute force (add all violated cuts).
    With a scorer, each round keeps only the top `topfrac` of candidates by score.
    Returns (refuted, cons, cut_derivs, added, reason).  `added` is the per-cut
    record [(viol, mults, q, cut, cons_index)] for imitation."""
    cons = list(inputs)
    seen = {c.canonical().key() for c in cons}
    rng = np.random.default_rng(seed)
    cut_derivs, added = [], []
    t0 = time.time()
    for rnd in range(max_rounds):
        if time.time() - t0 > max_secs:
            return False, cons, cut_derivs, added, "timeout"
        objs = [None] + [list(rng.uniform(-1, 1, nvars)) for _ in range(n_obj - 1)]
        cand = {}                                         # dedup candidates by key
        for obj in objs:
            st, x = cp_lp.lp_point(cons, nvars, obj)
            if st == "infeasible":
                return True, cons, cut_derivs, added, time.time() - t0
            if st != "feasible":
                continue
            for viol, mults, q, cut in cp_lp.separate_all(cons, nvars, x, qmax):
                k = cut.canonical().key()
                if k in seen or k in cand:
                    continue
                cand[k] = (viol, mults, q, cut)
        if not cand:
            return False, cons, cut_derivs, added, "stuck"
        items = list(cand.values())
        if scorer is not None:                            # keep top-scored fraction
            items.sort(key=lambda t: -scorer(*t, nvars))
            items = items[:max(1, int(round(len(items) * topfrac)))]
        for viol, mults, q, cut in items:
            ci = len(cons)
            added.append((viol, mults, q, cut, ci))
            cut_derivs.append((mults, q)); cons.append(cut)
            seen.add(cut.canonical().key())
    return False, cons, cut_derivs, added, "max_rounds"


def record(tag, qmax=10, n_obj=6, max_rounds=40, seed=0):
    """Brute-force run → label each added cut useful/not via the Farkas trace."""
    inputs = cp.read_cnf(cnf_path(tag))
    nvars = max(v for c in inputs for v in c.coef)
    t0 = time.time()
    refuted, cons, cut_derivs, added, reason = _rounds(
        inputs, nvars, qmax, n_obj, max_rounds, seed)
    if not refuted:
        print(f"  record {tag}: NOT refuted ({reason}, {len(added)} cuts)")
        return None
    mult = cp_lp.farkas_refute(cons)
    if not mult:
        print(f"  record {tag}: refuted but final Farkas failed")
        return None
    useful = compute_useful(len(inputs), cut_derivs, mult)
    X = np.array([cut_feats(v, m, q, c, nvars) for (v, m, q, c, ci) in added])
    y = np.array([1.0 if ci in useful else 0.0 for (v, m, q, c, ci) in added])
    print(f"  record {tag}: {len(y)} cuts added, {int(y.sum())} useful "
          f"({y.mean():.0%}), {time.time()-t0:.0f}s")
    return X, y


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--train", nargs="+", default=["3_2", "4_3"])
    ap.add_argument("--eval", nargs="+", default=["4_3", "5_4"])
    ap.add_argument("--topfrac", type=float, default=0.4)
    ap.add_argument("--qmax", type=int, default=10)
    ap.add_argument("--max-secs", type=int, default=120)
    args = ap.parse_args()

    print("=== recording imitation data (brute-force loop + Farkas trace) ===")
    data = [d for d in (record(t, qmax=args.qmax) for t in args.train) if d]
    if not data:
        print("no usable training data"); return
    X = np.vstack([d[0] for d in data]); y = np.concatenate([d[1] for d in data])
    if len(np.unique(y)) < 2:
        print(f"DEGENERATE: all-{int(y[0])} labels — cannot train a scorer."); return
    mu, sd = standardize(X)
    w, b = logreg_fit((X - mu) / sd, y, l2=1.0)
    print(f"\ntrained on {len(y)} cuts ({int(y.sum())} useful). "
          f"weights (standardized; + ⇒ keep):")
    for nm, wi in sorted(zip(FEAT_NAMES, w), key=lambda t: -abs(t[1])):
        print(f"  {nm:9} {wi:+.3f}")

    def scorer(viol, mults, q, cut, nvars):
        z = np.clip((np.array(cut_feats(viol, mults, q, cut, nvars)) - mu) / sd,
                    -10, 10)
        return float(z @ w + b)

    print(f"\n=== eval: policy (top {args.topfrac:.0%}/round) vs brute force ===")
    base = {"3_2": 8, "4_3": 12}                          # brute-force cut counts
    for t in args.eval:
        inputs = cp.read_cnf(cnf_path(t))
        nvars = max(v for c in inputs for v in c.coef)
        t0 = time.time()
        refuted, _, cd, _, reason = _rounds(inputs, nvars, args.qmax, 6, 60, 0,
                                            scorer=scorer, topfrac=args.topfrac,
                                            max_secs=args.max_secs)
        where = "in-sample" if t in args.train else "OUT-OF-SAMPLE"
        bf = base.get(t, "?(slow)")
        verdict = (f"refuted in {len(cd)} cuts ({time.time()-t0:.0f}s)"
                   if refuted else f"NOT refuted ({reason}, {len(cd)} cuts)")
        print(f"  PHP-{t.replace('_','-')} [{where}]: policy {verdict}  "
              f"vs brute force {bf} cuts")


if __name__ == "__main__":
    main()
