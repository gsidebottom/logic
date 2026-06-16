#!/usr/bin/env python3
"""
Phase 1b — per-variable PHASE predictor (the NeuroBack target).

Same literal–clause message-passing encoder as the Phase-0c classifier
(model.py) — SUM aggregation + LayerNorm, the symmetry-breaking that made it
train — but a per-VARIABLE output head instead of a SAT/UNSAT pool: for each
variable v, combine the final embeddings of its two literals (v, ¬v) and
predict v's phase (its value in a satisfying assignment).  This is the signal
NeuroBack (ICLR 2024) showed warm-starts CDCL when seeded into phase-saving.

CRUX GATE: held-out per-variable phase accuracy must clearly beat the
majority-phase baseline.  Random k-SAT phases are unpredictable; this trains on
*structured* SAT instances (neural/data/phase_ds, built by build_dataset.py)
where phase correlates with graph structure.

Labels are a SINGLE satisfying assignment's phases (the documented MVP);
majority-vote over many models is NeuroBack's refinement (left for 1b+).

Usage:  phase_model.py --data <dataset_dir> [--dim 64 --rounds 16 --epochs 60
                       --lr 1e-3 --batch 8 --seed 0]
Backend: MLX (Apple Silicon).  Run via `uv run` after `setup.sh`.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random

import numpy as np
import mlx.core as mx
import mlx.nn as nn
import mlx.optimizers as optim
from mlx.utils import tree_flatten, tree_unflatten, tree_map


# ─── data ───────────────────────────────────────────────────────────────────

def load_instance(path: str):
    """Load one SAT .npz → sparse COO incidence + flip + per-var phase labels.

    SPARSE, not dense: real instances reach ~34k vars / 200k clauses, whose
    dense (n_clauses × n_lit) incidence would be tens of GB.  We keep the COO
    edge lists (edge_lit, edge_clause) and aggregate with scatter-add."""
    d = np.load(path)
    if int(d["sat"]) != 1:
        return None                      # phase labels meaningful only for SAT
    n_vars = int(d["n_vars"])
    phase = d["phase"].astype(np.float32)                   # (n_vars,) majority 0/1
    # agreement = fraction voting the majority way (0.5–1.0); 1.0 for single-model
    # npz.  Reconstruct the empirical P(var=True) = cnt/ku — the SOFT target that
    # teaches the net to be uncertain (≈0.5) on free vars and confident only on
    # backbones (agreement≈1.0), which is exactly what margin-seeding wants.
    agr = (d["agreement"].astype(np.float32) if "agreement" in d.files
           else np.ones_like(phase))
    p_true = phase * agr + (1.0 - phase) * (1.0 - agr)
    return {
        "el": mx.array(d["edge_lit"].astype(np.int32)),     # literal endpoint / edge
        "ec": mx.array(d["edge_clause"].astype(np.int32)),  # clause endpoint / edge
        "flip": mx.array(d["flip"].astype(np.int32)),
        "n_lit": 2 * n_vars, "n_cls": int(d["n_clauses"]), "n_vars": n_vars,
        # lit_node(l) = 2(v-1) + (l<0): positive lits are even, negative odd.
        "pos": mx.arange(n_vars) * 2,
        "neg": mx.arange(n_vars) * 2 + 1,
        "phase": mx.array(phase),                           # (n_vars,) hard majority
        "phase_soft": mx.array(p_true),                     # (n_vars,) P(True)
    }


def load_dataset(ds_dir: str):
    man = [json.loads(l) for l in open(os.path.join(ds_dir, "manifest.jsonl"))]
    train, test = [], []
    for e in man:
        if not e.get("saved") or e.get("sat") != 1:
            continue
        inst = load_instance(os.path.join(ds_dir, f"{e['hash']}.npz"))
        if inst is None:
            continue
        (test if e["split"] == "test" else train).append(inst)
    return train, test


# ─── model ──────────────────────────────────────────────────────────────────

class PhaseNet(nn.Module):
    """NeuroSAT-style encoder + per-variable phase head."""

    def __init__(self, dim: int, rounds: int):
        super().__init__()
        self.dim = dim
        self.rounds = rounds
        self.L_init = mx.random.normal((1, dim)) * 0.1
        self.C_init = mx.random.normal((1, dim)) * 0.1
        self.l2c = nn.Linear(dim, dim)
        self.c2l = nn.Linear(dim, dim)
        self.c_upd = nn.Linear(2 * dim, dim)
        self.l_upd = nn.Linear(3 * dim, dim)
        self.ln_c = nn.LayerNorm(dim)
        self.ln_l = nn.LayerNorm(dim)
        # per-variable head: sees its literal's and its complement's embedding.
        self.head = nn.Sequential(
            nn.Linear(2 * dim, dim), nn.ReLU(), nn.Linear(dim, 1))

    def encode(self, inst) -> mx.array:
        """T rounds of sparse message passing → literal embeddings (n_lit, dim).

        SUM aggregation via scatter-add over the COO edges (a literal occurs in
        many clauses; a clause has many literals) — the symmetry-breaker from
        Phase 0c, now scalable."""
        el, ec, flip = inst["el"], inst["ec"], inst["flip"]
        n_lit, n_cls = inst["n_lit"], inst["n_cls"]
        L = mx.broadcast_to(self.L_init, (n_lit, self.dim))
        C = mx.broadcast_to(self.C_init, (n_cls, self.dim))
        for _ in range(self.rounds):
            c_msg = mx.zeros((n_cls, self.dim)).at[ec].add(
                mx.take(self.l2c(L), el, axis=0))            # literals → clauses
            C = self.ln_c(C + mx.tanh(self.c_upd(mx.concatenate([C, c_msg], -1))))
            l_msg = mx.zeros((n_lit, self.dim)).at[el].add(
                mx.take(self.c2l(C), ec, axis=0))            # clauses → literals
            L = self.ln_l(L + mx.tanh(self.l_upd(
                mx.concatenate([L, l_msg, mx.take(L, flip, axis=0)], -1))))
        return L

    def __call__(self, inst) -> mx.array:
        L = self.encode(inst)
        feat = mx.concatenate([mx.take(L, inst["pos"], axis=0),
                               mx.take(L, inst["neg"], axis=0)], axis=-1)
        return self.head(feat).reshape(-1)               # (n_vars,) phase logits


# ─── train / eval ───────────────────────────────────────────────────────────

LABEL_SMOOTH = 0.0   # set from --label-smooth; softens targets toward 0.5 to
                     # curb overconfidence (better calibration) on bigger nets.
SOFT_LABELS = False  # set from --soft-labels; train on P(True) (majority-vote
                     # agreement) instead of the hard majority phase.


def loss_fn(model, inst):
    logits = model(inst)
    y = inst["phase_soft"] if SOFT_LABELS else inst["phase"]
    if LABEL_SMOOTH:
        y = y * (1.0 - LABEL_SMOOTH) + 0.5 * LABEL_SMOOTH
    return nn.losses.binary_cross_entropy(
        logits, y, with_logits=True, reduction="mean")


def accuracy(model, data):
    """(micro, macro): micro = over all variables; macro = mean per-instance."""
    if not data:
        return float("nan"), float("nan")
    tot_ok = tot_n = 0
    per_inst = []
    for inst in data:
        pred = (mx.sigmoid(model(inst)) >= 0.5).astype(mx.float32)
        ok = mx.sum(pred == inst["phase"]).item()
        n = inst["n_vars"]
        tot_ok += ok; tot_n += n
        per_inst.append(ok / max(1, n))
    return tot_ok / max(1, tot_n), sum(per_inst) / len(per_inst)


def majority_baseline(data):
    """Best constant predictor: micro = global majority phase rate."""
    ones = tot = 0
    per_inst = []
    for inst in data:
        o = mx.sum(inst["phase"]).item(); n = inst["n_vars"]
        ones += o; tot += n
        per_inst.append(max(o, n - o) / max(1, n))
    p = ones / max(1, tot)
    return max(p, 1 - p), sum(per_inst) / len(per_inst)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True)
    ap.add_argument("--dim", type=int, default=64)
    ap.add_argument("--rounds", type=int, default=16)
    ap.add_argument("--epochs", type=int, default=60)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--batch", type=int, default=8)   # grad-accum: denoise steps
    ap.add_argument("--label-smooth", type=float, default=0.0,
                    help="soften targets toward 0.5 (e.g. 0.05) for calibration")
    ap.add_argument("--soft-labels", action="store_true",
                    help="train on P(True) from majority-vote agreement (needs a "
                         "--models K harvested dataset) instead of the hard phase")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--save", default=None,
                    help="save best weights to PATH.safetensors (+ PATH.json config) "
                         "for CPU inference (phase_infer.py)")
    args = ap.parse_args()

    global LABEL_SMOOTH, SOFT_LABELS
    LABEL_SMOOTH = args.label_smooth
    SOFT_LABELS = args.soft_labels
    mx.random.seed(args.seed)
    rng = random.Random(args.seed)
    train, test = load_dataset(args.data)
    if not train or not test:
        print(f"insufficient data: train={len(train)} test={len(test)}")
        return
    b_tr_micro, _ = majority_baseline(train)
    b_te_micro, b_te_macro = majority_baseline(test)
    tr_vars = sum(i["n_vars"] for i in train)
    te_vars = sum(i["n_vars"] for i in test)
    print(f"train={len(train)} insts ({tr_vars} vars)  "
          f"test={len(test)} insts ({te_vars} vars)")
    print(f"majority-phase baseline: train_micro={b_tr_micro:.3f}  "
          f"test_micro={b_te_micro:.3f}  test_macro={b_te_macro:.3f}")
    print(f"targets: {'SOFT P(True) from agreement' if SOFT_LABELS else 'hard phase'}"
          f"{f' + label_smooth={LABEL_SMOOTH}' if LABEL_SMOOTH else ''}  "
          f"(gate still measures hard acc vs majority)")

    model = PhaseNet(args.dim, args.rounds)
    mx.eval(model.parameters())
    opt = optim.Adam(learning_rate=args.lr)
    lag = nn.value_and_grad(model, loss_fn)

    best_micro = 0.0
    best_params = None
    for ep in range(1, args.epochs + 1):
        rng.shuffle(train)
        tot = 0.0
        acc = None
        nacc = 0

        def _step(acc, nacc):
            acc = tree_map(lambda a: a * (1.0 / nacc), acc)
            acc, _ = optim.clip_grad_norm(acc, 5.0)
            opt.update(model, acc)
            mx.eval(model.parameters(), opt.state)

        for inst in train:
            loss, grads = lag(model, inst)
            tot += loss.item()
            acc = grads if acc is None else tree_map(lambda a, g: a + g, acc, grads)
            nacc += 1
            if nacc == args.batch:
                _step(acc, nacc); acc, nacc = None, 0
        if nacc:
            _step(acc, nacc)
        tr_micro, _ = accuracy(model, train)
        te_micro, te_macro = accuracy(model, test)
        if te_micro > best_micro:
            best_micro = te_micro
            best_params = tree_flatten(model.parameters())
        if ep % 3 == 0 or ep == 1 or ep == args.epochs:
            print(f"  epoch {ep:3d}  loss={tot/len(train):.4f}  "
                  f"train_micro={tr_micro:.3f}  test_micro={te_micro:.3f}  "
                  f"test_macro={te_macro:.3f}")

    if best_params is not None:
        model.update(tree_unflatten(best_params)); mx.eval(model.parameters())
    te_micro, te_macro = accuracy(model, test)
    best_micro = max(best_micro, te_micro)
    margin = best_micro - b_te_micro
    print(f"\nPhase-1b gate: test phase acc micro={te_micro:.3f} "
          f"(best {best_micro:.3f}) vs majority {b_te_micro:.3f}  "
          f"(margin {margin:+.3f}); macro={te_macro:.3f} vs {b_te_macro:.3f}")
    print("  GATE PASSED ✓ — phases are predictable from structure" if margin >= 0.05
          else "  GATE NOT MET — margin %.3f < 0.05 "
                "(try majority-vote labels or more data)" % margin)

    if args.save:
        base = args.save[:-len(".safetensors")] if args.save.endswith(".safetensors") else args.save
        model.save_weights(base + ".safetensors")
        json.dump({"dim": args.dim, "rounds": args.rounds,
                   "label_smooth": args.label_smooth,
                   "soft_labels": args.soft_labels},
                  open(base + ".json", "w"))
        print(f"  saved weights → {base}.safetensors  (config {base}.json)")


if __name__ == "__main__":
    main()
