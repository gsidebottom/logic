#!/usr/bin/env python3
"""
Calibration probe for a phase predictor — does confidence track accuracy?

The v6 A/B regressions came from *confident-but-wrong* predicted phases. The
margin filter (phase_infer.py --margin M: seed v iff 2*|p-0.5| >= M) can only
suppress those if the model is CALIBRATED — i.e. high-confidence predictions are
actually more accurate. This probe quantifies that on a labeled held-out split:

  - reliability bins (confidence vs empirical accuracy) + ECE
  - accuracy-at-margin: for each M, coverage (fraction seeded) and the accuracy
    of the seeded variables. The crux: does acc_seeded RISE with M?

Usage:  calibrate.py --weights neural/weights/phase_v6 --data data/phase_ds_v6
"""
from __future__ import annotations
import argparse, os, sys
import numpy as np
import mlx.core as mx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phase_model import PhaseNet, load_dataset, majority_baseline  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--weights", required=True)
    ap.add_argument("--data", required=True, help="dataset dir (uses split==test)")
    ap.add_argument("--cpu", action="store_true")
    ap.add_argument("--split", default="test", choices=["test", "train"])
    args = ap.parse_args()
    if args.cpu:
        mx.set_default_device(mx.cpu)

    import json
    cfg = json.load(open(args.weights + ".json"))
    model = PhaseNet(cfg["dim"], cfg["rounds"])
    model.load_weights(args.weights + ".safetensors")
    mx.eval(model.parameters())

    train, test = load_dataset(args.data)
    data = test if args.split == "test" else train
    print(f"model {os.path.basename(args.weights)} (dim={cfg['dim']} "
          f"rounds={cfg['rounds']}) on {args.data} [{args.split}]: "
          f"{len(data)} instances")

    # gather per-variable (prob_of_True, label) across all instances
    probs, labels = [], []
    for inst in data:
        p = np.array(mx.sigmoid(model(inst)))            # P(phase=True)
        probs.append(p)
        labels.append(np.array(inst["phase"]))
    p = np.concatenate(probs)
    y = np.concatenate(labels)
    n = len(y)
    pred = (p >= 0.5)
    correct = (pred == (y >= 0.5))
    conf_pred = np.where(pred, p, 1 - p)                 # prob of predicted class
    conf = 2.0 * np.abs(p - 0.5)                         # 0..1 margin-confidence

    mic = correct.mean()
    bmic, _ = majority_baseline(data)
    print(f"\nmicro acc = {mic:.3f}   majority = {bmic:.3f}   "
          f"margin = {mic - bmic:+.3f}   (N={n} vars)")

    # ── reliability + ECE (10 equal-width bins on conf_pred in [0.5,1]) ──
    print("\nreliability (predicted-class prob vs empirical accuracy):")
    print(f"  {'prob bin':>12} {'count':>8} {'mean_prob':>10} {'acc':>8} {'gap':>8}")
    ece = 0.0
    edges = np.linspace(0.5, 1.0 + 1e-9, 11)
    for lo, hi in zip(edges[:-1], edges[1:]):
        m = (conf_pred >= lo) & (conf_pred < hi)
        if not m.any():
            continue
        cb, ab = conf_pred[m].mean(), correct[m].mean()
        ece += (m.sum() / n) * abs(ab - cb)
        print(f"  [{lo:.2f},{hi:.2f}) {m.sum():>8} {cb:>10.3f} {ab:>8.3f} "
              f"{ab - cb:>+8.3f}")
    print(f"  ECE = {ece:.4f}   (0 = perfectly calibrated)")

    # ── accuracy-at-margin: the crux table ──
    print("\naccuracy-at-margin (seed v iff 2*|p-0.5| >= M):")
    print(f"  {'M':>5} {'coverage':>10} {'n_seeded':>9} {'acc_seeded':>11}")
    for M in [0.0, 0.3, 0.5, 0.6, 0.7, 0.8, 0.9, 0.95]:
        keep = conf >= M
        cov = keep.mean()
        acc = correct[keep].mean() if keep.any() else float("nan")
        print(f"  {M:>5.2f} {cov:>10.3f} {int(keep.sum()):>9} {acc:>11.3f}")
    print("\n  → if acc_seeded RISES with M, the margin filter suppresses bad "
          "seeds (lever: bigger model + higher margin).\n  → if it stays FLAT, "
          "the model is miscalibrated (lever: calibration).")


if __name__ == "__main__":
    main()
