#!/usr/bin/env python3
"""
Probe-gate (solver-dynamics) strategies — wall/CPU tradeoff, simulated.

The catastrophic warm-start regressions are invisible to the predictor's output
(see gate_loo.py) but are trivially visible to the SOLVER: just race seeded vs
unseeded for a short probe and take the first to finish. The race outcome
depends only on which of base_s / warm_s is smaller and whether it beats the
probe budget T_p — both already measured in the ungated A/B — so every strategy
here is simulated exactly (then spot-checked with real concurrent runs).

Strategies (per instance, given base_s b, warm_s w, probe budget T_p):
  - portfolio (T_p=inf): run both to completion, first wins.
        wall = min(b,w)               cpu = 2*min(b,w)
  - probe+commit-seeded: run both until first finishes OR T_p; if neither
    finished by T_p, kill unseeded and let seeded finish (the bet).
        min(b,w) <= T_p:  wall = min(b,w),  cpu = 2*min(b,w)
        else:             wall = w,         cpu = w + T_p
  - probe+commit-unseeded: same but the safe default commits to UNSEEDED.
        else:             wall = b,         cpu = b + T_p

Reference: baseline (skip all = b), ungated (seed all = w), oracle (= min(b,w)).
Input: /tmp/gate_data.json (has base_s, warm_s per instance).
"""
from __future__ import annotations
import json, sys
import numpy as np


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "/tmp/gate_data.json"
    data = [d for d in json.load(open(path)) if d["base_conf"] > 0]
    b = np.array([d["base_s"] for d in data])
    w = np.array([d["warm_s"] for d in data])
    mn = np.minimum(b, w)
    base, ungated, oracle = b.sum(), w.sum(), mn.sum()
    n = len(data)

    def line(tag, wall, cpu):
        print(f"  {tag:30} wall={wall:7.1f}s ({100*(wall-base)/base:+5.1f}%)   "
              f"cpu={cpu:7.1f}s ({cpu/base:.2f}x baseline)")

    print(f"probe-gate tradeoff on {n} non-trivial held-out instances")
    print(f"  (baseline skip-all={base:.1f}s; ungated seed-all={ungated:.1f}s "
          f"= {100*(ungated-base)/base:+.1f}%; oracle min={oracle:.1f}s "
          f"= {100*(oracle-base)/base:+.1f}%)\n")
    line("ungated (seed all, 1x)", ungated, ungated)
    line("portfolio to completion", oracle, 2 * mn.sum())
    print()
    for tp in (5, 10, 15, 20, 30, 45, 60):
        slow = mn > tp                                   # neither finished by T_p
        wall_s = np.where(slow, w, mn).sum()             # commit seeded if both slow
        cpu_s = np.where(slow, w + tp, 2 * mn).sum()
        line(f"probe T_p={tp:>2}s, commit-seeded", wall_s, cpu_s)
    print()
    for tp in (10, 20, 30):
        slow = mn > tp
        wall_u = np.where(slow, b, mn).sum()             # commit unseeded if both slow
        cpu_u = np.where(slow, b + tp, 2 * mn).sum()
        line(f"probe T_p={tp:>2}s, commit-unseeded", wall_u, cpu_u)
    print()
    print(f"  reference: threshold gate (1x cpu) was ~-4 to -6% wall.")
    print(f"  # instances where both arms > T_p (the 'commit' cases):")
    for tp in (5, 10, 15, 20, 30, 45, 60):
        print(f"    T_p={tp:>2}s: {int((mn>tp).sum()):>2}/{n}")


if __name__ == "__main__":
    main()
