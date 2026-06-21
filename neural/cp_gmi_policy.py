#!/usr/bin/env python3
"""
Learned cut-SELECTION policy for the GMI engine (the Aristotle analog on
cutting-planes).  The warm-start engine is fast enough that the bottleneck is now
the CUT COUNT (php-9-8 needs ~1810 cuts) — but the final Farkas refutation only
*uses* a fraction of them.  Imitation:

  1. run the add-all GMI loop; trace the final Farkas support backward through the
     cut derivations (each cut's `lamC` names its source constraints) → label every
     added cut useful / not;
  2. fit a logistic scorer over cheap per-cut features;
  3. re-run keeping only the top-scored fraction of cuts per round → fewer cuts,
     smaller proof, still veripb-VERIFIED.

This mirrors `cp_cut_policy.py` (which did this for the *incomplete* mod-q
separator) on the *complete* exact-Gomory separator, and is the per-step hook a
later GNN / expert-iteration would slot into.

Usage:  cp_gmi_policy.py --measure 4_3 5_4 6_5
        cp_gmi_policy.py --train 3_2 4_3 5_4 --eval 5_4 6_5 --topfrac 0.5
"""
from __future__ import annotations
import argparse, os, sys, tempfile, time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cp_search as cp                                    # noqa: E402
import cp_lp                                              # noqa: E402
import cp_gmi                                             # noqa: E402
from cp_policy import logreg_fit, standardize            # noqa: E402

FEAT_NAMES = ["viol", "D", "nsrc", "nbound", "msum", "degree", "ncoef",
              "maxc", "density"]
TD = tempfile.mkdtemp(prefix="gmipol_")


def cnf_for(tag):
    P, H = tag.split("_")
    path = os.path.join(TD, f"php_{tag}.cnf")
    if not os.path.exists(path):
        cp_gmi.php_cnf(int(P), int(H), path)
    return path


def cut_feats(viol, cut, recipe, nvars):
    """Cheap intrinsic features of a candidate Gomory cut (no engine state)."""
    D, lam_c, lam_l, lam_b = recipe
    coefs = [abs(a) for a in cut.coef.values()]
    allm = list(lam_c.values()) + list(lam_l.values()) + list(lam_b.values())
    return [float(viol), float(D), float(len(lam_c)), float(len(lam_l) + len(lam_b)),
            float(sum(allm)), float(abs(cut.rhs)), float(len(cut.coef)),
            float(max(coefs) if coefs else 0), len(cut.coef) / max(1, nvars)]


def compute_useful(n_inputs, recipes, mult):
    """Cons-indices in the TRANSITIVE Farkas support: nonzero-multiplier
    constraints, plus every constraint a useful cut was derived from (each cut's
    recipe `lamC` keys are its source cons-indices; walk backward)."""
    useful = {j for j in range(len(mult)) if abs(mult[j]) > 1e-9}
    for k in range(len(recipes) - 1, -1, -1):             # cut k lives at n_inputs+k
        if (n_inputs + k) in useful:
            useful.update(recipes[k][1].keys())           # lamC source cons-indices
    return useful


def gmi_rounds(inputs, nvars, scorer=None, topfrac=1.0, n_obj=4, max_rounds=120,
               seed=0, max_secs=300):
    """GMI cutting-plane loop with optional cut SELECTION.  Each round gathers the
    distinct violated Gomory cuts across n_obj rotated objectives; with a scorer,
    keeps only the top `topfrac`.  Returns (refuted, cons, recipes, added, reason)
    where added[k]=(viol, cut, recipe, cons_index, feats)."""
    cons = list(inputs)
    seen = {c.canonical().key() for c in cons}
    recipes, added = [], []
    rng = np.random.default_rng(seed)
    t0 = time.time()
    for _ in range(max_rounds):
        if time.time() - t0 > max_secs:
            return False, cons, recipes, added, "timeout"
        objs = [None] + [list(rng.uniform(-1, 1, nvars)) for _ in range(n_obj - 1)]
        cand = {}
        for obj in objs:
            std = cp_gmi.Standard(cons, nvars)
            status, T, b, basis = cp_gmi.solve(std, obj)
            if status == "infeasible":
                return True, cons, recipes, added, "refuted"
            x = cp_gmi.primal(std, b, basis)
            for viol, cut, recipe in cp_gmi.gomory_cuts(std, T, b, basis, x):
                k = cut.canonical().key()
                if k not in seen and k not in cand:
                    cand[k] = (viol, cut, recipe)
        if not cand:
            return False, cons, recipes, added, "stuck"
        items = list(cand.values())
        if scorer is not None:
            items.sort(key=lambda t: -scorer(t[0], t[1], t[2], nvars))
            items = items[:max(1, int(round(len(items) * topfrac)))]
        for viol, cut, recipe in items:
            ci = len(cons)
            added.append((viol, cut, recipe, ci, cut_feats(viol, cut, recipe, nvars)))
            recipes.append(recipe)
            cons.append(cut)
            seen.add(cut.canonical().key())
    return False, cons, recipes, added, "max_rounds"


def record(tag, **kw):
    """Add-all run → (X feats, y useful-labels) plus a summary."""
    path = cnf_for(tag)
    inputs = cp.read_cnf(path)
    nvars = max(v for c in inputs for v in c.coef)
    t0 = time.time()
    refuted, cons, recipes, added, reason = gmi_rounds(inputs, nvars, **kw)
    if not refuted:
        print(f"  {tag}: NOT refuted ({reason}, {len(added)} cuts)")
        return None
    mult = cp_lp.farkas_refute(cons)
    if not mult:
        print(f"  {tag}: refuted but final Farkas failed")
        return None
    useful = compute_useful(len(inputs), recipes, mult)
    X = np.array([f for (_, _, _, _, f) in added])
    y = np.array([1.0 if ci in useful else 0.0 for (_, _, _, ci, _) in added])
    print(f"  {tag}: {len(y)} cuts, {int(y.sum())} useful ({y.mean():.0%}), "
          f"{time.time() - t0:.1f}s")
    return X, y


def make_scorer(w, b, mu, sd):
    def scorer(viol, cut, recipe, nvars):
        z = np.clip((np.array(cut_feats(viol, cut, recipe, nvars)) - mu) / sd, -10, 10)
        return float(z @ w + b)
    return scorer


def evaluate(tag, scorer, topfrac, max_secs=300):
    """Re-run with the scorer (top topfrac/round); emit + veripb; report cuts."""
    path = cnf_for(tag)
    inputs = cp.read_cnf(path)
    nvars = max(v for c in inputs for v in c.coef)
    t0 = time.time()
    refuted, cons, recipes, added, reason = gmi_rounds(
        inputs, nvars, scorer=scorer, topfrac=topfrac, max_secs=max_secs)
    if not refuted:
        print(f"  {tag}: NOT refuted with policy ({reason}, {len(recipes)} cuts)")
        return
    mult = cp_lp.farkas_refute(cons)
    ok = False
    if mult:
        pbp = path + ".pol.pbp"
        cp_gmi.emit_gmi(len(inputs), recipes, mult, pbp)
        ok, _ = cp.verify(path, pbp)
    print(f"  {tag}: policy {len(recipes)} cuts ({time.time()-t0:.1f}s) -> "
          f"veripb {'VERIFIED' if ok else 'FAILED'}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--measure", nargs="*", default=[])
    ap.add_argument("--train", nargs="*", default=[])
    ap.add_argument("--eval", nargs="*", default=[])
    ap.add_argument("--topfrac", type=float, default=0.5)
    ap.add_argument("--max-secs", type=float, default=300)
    args = ap.parse_args()

    if args.measure:
        print("=== useful-cut fraction (add-all) ===")
        for tag in args.measure:
            record(tag, max_secs=args.max_secs)
        return

    print("=== train (add-all, label by Farkas support) ===")
    Xs, ys = [], []
    for tag in args.train:
        r = record(tag, max_secs=args.max_secs)
        if r:
            Xs.append(r[0]); ys.append(r[1])
    X = np.vstack(Xs); y = np.concatenate(ys)
    mu, sd = standardize(X)
    Z = np.clip((X - mu) / sd, -10, 10)
    w, b = logreg_fit(Z, y)
    print("  weights:", {n: round(float(wi), 2) for n, wi in zip(FEAT_NAMES, w)})
    eff = w / sd                                           # rank-relevant raw weights
    print("  eff (w/sd) for Rust port:",
          "[" + ", ".join(f"{e:.6f}" for e in eff) + "]")
    scorer = make_scorer(w, b, mu, sd)

    print(f"=== eval (policy top {args.topfrac:.0%}/round) ===")
    base = {}
    for tag in args.eval:
        r = record(tag, max_secs=args.max_secs)             # add-all baseline
        base[tag] = "?" if r is None else len(r[1])
    for tag in args.eval:
        print(f"  [add-all {tag}: {base[tag]} cuts]")
        evaluate(tag, scorer, args.topfrac, max_secs=args.max_secs)


if __name__ == "__main__":
    main()
