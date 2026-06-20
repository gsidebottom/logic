#!/usr/bin/env python3
"""
Phase-3 step 2a — feature-based LEARNED priority for the CP proof search.

Imitation: run the slack-heuristic search on instances it solves, record every
expanded constraint's features + whether it ends up on the proof path, and fit a
logistic scorer (features -> P(on-path)). Use that score as the best-first
priority and compare node counts to the slack baseline. The learned WEIGHTS are
diagnostic: if the scorer just re-discovers slack, the feature approach adds
nothing (-> need a GNN over the constraint graph); if it weights structure slack
misses, a learned policy is worth building.

Usage: cp_policy.py [--train 3_2 4_3] [--eval 4_3 5_4] [--max-nodes N]
"""
from __future__ import annotations
import argparse, os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cp_search as cp


def logreg_fit(X, y, l2=1.0, iters=1500, lr=0.1):
    """L2 logistic regression with clipped logits + gradient clipping
    (a near-constant standardized feature otherwise diverges to NaN)."""
    n, d = X.shape
    w = np.zeros(d); b = 0.0
    with np.errstate(over="ignore", divide="ignore", invalid="ignore"):
        for _ in range(iters):                        # macOS Accelerate emits
            z = np.clip(X @ w + b, -30.0, 30.0)       # spurious matmul warnings;
            g = 1.0 / (1.0 + np.exp(-z)) - y          # clip+grad-clip keep w finite
            gw = X.T @ g / n + l2 * w / n
            gb = float(g.mean())
            gn = float(np.sqrt((gw ** 2).sum() + gb * gb))
            if gn > 5.0:                               # gradient clip
                gw *= 5.0 / gn; gb *= 5.0 / gn
            w -= lr * gw; b -= lr * gb
    return w, b


def standardize(X):
    mu = X.mean(0)
    sd = X.std(0)
    sd[sd < 1e-6] = 1.0                                # near-constant ⇒ unit scale
    return mu, sd


def cnf_path(tag):
    return f"/tmp/php_{tag}/php_{tag}.cnf"


def record(tag, max_nodes):
    inputs = cp.read_cnf(cnf_path(tag))
    t0 = time.time()
    contra, nodes, popped, _ = cp.search(inputs, max_nodes, allow_divide=True,
                                         same_sign=False, record=True, max_secs=1200)
    if not contra:
        print(f"  record {tag}: NO PROOF ({nodes} nodes) — skipped")
        return None
    anc = cp.ancestors(contra)
    X = np.array([cp.feats(p) for p in popped])
    y = np.array([1.0 if id(p) in anc else 0.0 for p in popped])
    print(f"  record {tag}: {len(y)} expanded, {int(y.sum())} on-path, "
          f"{nodes} nodes, {time.time()-t0:.0f}s")
    return X, y


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--train", nargs="+", default=["3_2", "4_3"])
    ap.add_argument("--eval", nargs="+", default=["4_3"])
    ap.add_argument("--max-nodes", type=int, default=50000)
    args = ap.parse_args()

    cache = "/tmp/cp_train_" + "_".join(args.train) + ".npz"
    if os.path.exists(cache):
        d = np.load(cache); X, y = d["X"], d["y"]
        print(f"=== loaded cached imitation data: {len(y)} examples ({cache}) ===")
    else:
        print("=== recording imitation data ===")
        data = [record(t, args.max_nodes) for t in args.train]
        data = [d for d in data if d]
        X = np.vstack([d[0] for d in data]); y = np.concatenate([d[1] for d in data])
        np.savez(cache, X=X, y=y)
    if len(np.unique(y)) < 2:
        print(f"\nDEGENERATE training data: {len(y)} examples, all one class "
              f"({int(y.sum())} on-path). A discriminative scorer needs both "
              f"on-path AND off-path constraints (a recording that explored dead "
              f"ends). Aborting — would yield an all-zero scorer. Likely the "
              f"larger instance's recording failed; check the engine.")
        return
    mu, sd = standardize(X)
    w, b = logreg_fit((X - mu) / sd, y, l2=1.0)
    print(f"\ntrained on {len(y)} examples ({int(y.sum())} on-path). "
          f"feature weights (standardized; + ⇒ prioritize):")
    for nm, wi in sorted(zip(cp.FEAT_NAMES, w), key=lambda t: -abs(t[1])):
        print(f"  {nm:14} {wi:+.3f}")

    def prio(p):
        x = np.clip((np.array(cp.feats(p)) - mu) / sd, -10.0, 10.0)  # overflow-safe
        return (-float(x @ w + b),)         # higher score ⇒ popped first

    print("\n=== eval: learned priority vs slack baseline ===")
    baseline = {"3_2": 8, "4_3": 389}       # slack node counts
    for t in args.eval:
        inputs = cp.read_cnf(cnf_path(t))
        t0 = time.time()
        contra, nodes, _, _ = cp.search(inputs, args.max_nodes, allow_divide=True,
                                        same_sign=False, priority_fn=prio, max_secs=600)
        base = baseline.get(t, "?")
        tag = "in-sample" if t in args.train else "OUT-OF-SAMPLE"
        print(f"  PHP-{t.replace('_','-')} [{tag}]: learned "
              f"{'FOUND' if contra else 'NO PROOF'} in {nodes} nodes "
              f"({time.time()-t0:.0f}s)  vs slack {base} nodes")


if __name__ == "__main__":
    main()
