#!/usr/bin/env python3
"""
Learned per-instance gate — leave-one-out evaluation, no new solver runs.

The ungated v8@0.6 A/B already measured BOTH base_s and warm_s (and conflicts)
per instance, so any gate just *chooses* base (skip seeding) or warm (seed) for
each instance. We can therefore evaluate any gate by simulation. To avoid
circular fitting, the learned gate is trained leave-one-out: for each instance,
fit on the other N-1 and predict this one.

Compares total wall under: baseline (skip all), ungated (seed all), the coverage
THRESHOLD gate (skip if cov06 < FRAC), a LEARNED logistic gate (features →
P(seeding hurts), LOO), and an ORACLE gate (skip iff warm_s > base_s; the best
any gate could do). Input: /tmp/gate_data.json from the extraction step.

Usage: gate_loo.py [/tmp/gate_data.json]
"""
from __future__ import annotations
import json, sys
import numpy as np

FEATS = ["cov06", "cov08", "meanConf", "stdP", "fracTrue", "fracUnc",
         "skew", "seededMeanConf", "ratio"]


def logreg_fit(X, y, l2=1.0, iters=500, lr=0.3):
    """Tiny L2-regularized logistic regression (GD on standardized X)."""
    n, d = X.shape
    w = np.zeros(d); b = 0.0
    for _ in range(iters):
        z = X @ w + b
        p = 1.0 / (1.0 + np.exp(-z))
        g = p - y
        gw = X.T @ g / n + l2 * w / n
        gb = g.mean()
        w -= lr * gw; b -= lr * gb
    return w, b


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "/tmp/gate_data.json"
    data = [d for d in json.load(open(path)) if d["base_conf"] > 0]   # non-trivial
    n = len(data)
    base_s = np.array([d["base_s"] for d in data])
    warm_s = np.array([d["warm_s"] for d in data])
    hurt = np.array([1.0 if d["warm_conf"] > d["base_conf"] else 0.0 for d in data])  # conflict-regression (deterministic) label
    X = np.array([[d[f] for f in FEATS] for d in data])
    mu, sd = X.mean(0), X.std(0) + 1e-9
    Xs = (X - mu) / sd

    base_tot, ungated_tot = base_s.sum(), warm_s.sum()

    def wall(seed_mask):
        return float(np.where(seed_mask, warm_s, base_s).sum())

    def report(tag, seed_mask):
        w = wall(seed_mask); skipped = int((~seed_mask).sum())
        print(f"  {tag:24} wall={w:7.1f}s  ({100*(w-base_tot)/base_tot:+5.1f}%)  "
              f"seeded={int(seed_mask.sum())} skipped={skipped}")

    print(f"gate LOO on {n} non-trivial held-out instances "
          f"(baseline={base_tot:.1f}s, ungated seed-all={ungated_tot:.1f}s "
          f"= {100*(ungated_tot-base_tot)/base_tot:+.1f}%)")
    print("\n-- reference gates --")
    report("ungated (seed all)", np.ones(n, bool))
    cov06 = np.array([d["cov06"] for d in data])
    for frac in (0.10, 0.15):
        report(f"threshold cov<{frac}", cov06 >= frac)
    oracle = warm_s <= base_s
    report("ORACLE (skip if hurts)", oracle)

    # learned gate, leave-one-out
    pred_hurt = np.zeros(n)
    for i in range(n):
        tr = [j for j in range(n) if j != i]
        w, b = logreg_fit(Xs[tr], hurt[tr], l2=2.0)
        pred_hurt[i] = 1.0 / (1.0 + np.exp(-(Xs[i] @ w + b)))
    print("\n-- learned logistic gate (leave-one-out) --")
    for thr in (0.5, 0.4, 0.6):
        report(f"learned P(hurt)>{thr}", pred_hurt <= thr)

    # diagnostics: did it catch the high-confidence regressor 3c15c8fb?
    print("\n-- per-instance (sorted by wall delta) --")
    order = np.argsort(warm_s - base_s)[::-1]
    print(f"  {'instance':30} {'Δwall':>7} {'cov06':>6} {'P(hurt)':>7} {'thr.skip':>8} {'learn.skip':>10}")
    for i in order[:6]:
        d = data[i]
        print(f"  {d['name'][:30]:30} {warm_s[i]-base_s[i]:>+7.1f} {d['cov06']:>6.3f} "
              f"{pred_hurt[i]:>7.2f} {str(d['cov06']<0.10):>8} {str(pred_hurt[i]>0.5):>10}")


if __name__ == "__main__":
    main()
