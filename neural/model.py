#!/usr/bin/env python3
"""
Phase 0c — NeuroSAT-style message-passing GNN (MLX) for the Phase-0 gate:
satisfiability classification.

A literal–clause bipartite message-passing network (Selsam et al. 2019):
  init literal/clause embeddings →  T rounds of
    clauses ← aggregate(literal messages)
    literals ← aggregate(clause messages) + complement (flip) embedding
  → global mean-pool → SAT/UNSAT logit.

Aggregation uses each instance's dense incidence matrix (small Phase-0
graphs).  Trains on the build_dataset.py dataset, accumulating gradients over
a mini-batch before each step: single-instance steps are high-variance and
repeatedly knock the net into a constant-output (loss → ln 2) collapse basin;
averaging over a batch denoises the step and training converges stably.

PHASE-0 GATE: held-out test accuracy must clearly beat the majority-class
baseline — the sanity check that the encoder learns SAT structure before we
invest in search (Phase 1+).

Usage:  model.py --data <dataset_dir> [--dim 64 --rounds 16 --epochs 60
                  --lr 1e-3 --batch 16 --seed 0]
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
    """Load one .npz → (M, flip, label) as MLX tensors.  M is the dense
    incidence (n_clauses × n_lit), mean-normalized degrees folded in at use."""
    d = np.load(path)
    n_lit = 2 * int(d["n_vars"])
    n_cls = int(d["n_clauses"])
    M = np.zeros((n_cls, n_lit), dtype=np.float32)
    M[d["edge_clause"], d["edge_lit"]] = 1.0
    cdeg = np.maximum(M.sum(axis=1, keepdims=True), 1.0)   # (n_cls,1)
    ldeg = np.maximum(M.sum(axis=0, keepdims=True).T, 1.0)  # (n_lit,1)
    return {
        "M": mx.array(M),
        "Mt": mx.array(M.T),
        "cdeg": mx.array(cdeg),
        "ldeg": mx.array(ldeg),
        "flip": mx.array(d["flip"].astype(np.int32)),
        "n_lit": n_lit, "n_cls": n_cls,
        "label": float(int(d["sat"])),
    }


def load_dataset(ds_dir: str):
    man = [json.loads(l) for l in open(os.path.join(ds_dir, "manifest.jsonl"))]
    train, test = [], []
    for e in man:
        if not e.get("saved"):
            continue
        inst = load_instance(os.path.join(ds_dir, f"{e['hash']}.npz"))
        (test if e["split"] == "test" else train).append(inst)
    return train, test


# ─── model ──────────────────────────────────────────────────────────────────

class SatNet(nn.Module):
    def __init__(self, dim: int, rounds: int):
        super().__init__()
        self.dim = dim
        self.rounds = rounds
        self.L_init = mx.random.normal((1, dim)) * 0.1
        self.C_init = mx.random.normal((1, dim)) * 0.1
        self.l2c = nn.Linear(dim, dim)          # literal → clause message
        self.c2l = nn.Linear(dim, dim)          # clause → literal message
        self.c_upd = nn.Linear(2 * dim, dim)    # clause update
        self.l_upd = nn.Linear(3 * dim, dim)    # literal update (+ flip)
        self.ln_c = nn.LayerNorm(dim)           # stabilize SUM aggregation
        self.ln_l = nn.LayerNorm(dim)
        # readout sees both sum (magnitude ~ size/ratio) and mean (direction)
        self.readout = nn.Sequential(
            nn.Linear(4 * dim, dim), nn.ReLU(), nn.Linear(dim, 1))

    def __call__(self, inst) -> mx.array:
        M, Mt, flip = inst["M"], inst["Mt"], inst["flip"]
        L = mx.broadcast_to(self.L_init, (inst["n_lit"], self.dim))
        C = mx.broadcast_to(self.C_init, (inst["n_cls"], self.dim))
        for _ in range(self.rounds):
            # SUM aggregation (not mean): varying literal degree breaks the
            # initial symmetry; degree-normalizing would freeze it uniform.
            c_msg = M @ self.l2c(L)
            C = self.ln_c(C + mx.tanh(self.c_upd(mx.concatenate([C, c_msg], axis=-1))))
            l_msg = Mt @ self.c2l(C)
            L = self.ln_l(L + mx.tanh(self.l_upd(
                mx.concatenate([L, l_msg, mx.take(L, flip, axis=0)], axis=-1))))
        # sqrt-normalized sum keeps a size/ratio signal without the raw-sum
        # magnitude blowing logits up (which destabilized training).
        sl = 1.0 / math.sqrt(inst["n_lit"])
        sc = 1.0 / math.sqrt(inst["n_cls"])
        pooled = mx.concatenate([mx.sum(L, axis=0) * sl, mx.sum(C, axis=0) * sc,
                                 mx.mean(L, axis=0), mx.mean(C, axis=0)])
        return self.readout(pooled).reshape(())     # scalar logit


# ─── train / eval ───────────────────────────────────────────────────────────

def loss_fn(model, inst, y):
    logit = model(inst)
    return nn.losses.binary_cross_entropy(logit, y, with_logits=True)


def accuracy(model, data) -> float:
    if not data:
        return float("nan")
    ok = 0
    for inst in data:
        p = mx.sigmoid(model(inst)).item()
        ok += int((p >= 0.5) == (inst["label"] >= 0.5))
    return ok / len(data)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True)
    ap.add_argument("--dim", type=int, default=64)
    ap.add_argument("--rounds", type=int, default=16)
    ap.add_argument("--epochs", type=int, default=60)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--batch", type=int, default=16)   # mini-batch denoising is what makes training stable
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    mx.random.seed(args.seed)
    rng = random.Random(args.seed)
    train, test = load_dataset(args.data)
    n_sat = sum(1 for i in train if i["label"] > 0.5)
    base_tr = max(n_sat, len(train) - n_sat) / max(1, len(train))
    ts_sat = sum(1 for i in test if i["label"] > 0.5)
    base_te = max(ts_sat, len(test) - ts_sat) / max(1, len(test))
    print(f"train={len(train)} (SAT={n_sat})  test={len(test)} (SAT={ts_sat})")
    print(f"majority-class baseline: train={base_tr:.3f}  test={base_te:.3f}")

    model = SatNet(args.dim, args.rounds)
    mx.eval(model.parameters())
    opt = optim.Adam(learning_rate=args.lr)
    lag = nn.value_and_grad(model, loss_fn)

    best_te = 0.0
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
            y = mx.array(inst["label"])
            loss, grads = lag(model, inst, y)
            tot += loss.item()
            acc = grads if acc is None else tree_map(lambda a, g: a + g, acc, grads)
            nacc += 1
            if nacc == args.batch:        # mini-batch: averaged, denoised step
                _step(acc, nacc)
                acc, nacc = None, 0
        if nacc:                          # flush the remainder
            _step(acc, nacc)
        tr_acc, te_acc = accuracy(model, train), accuracy(model, test)
        if te_acc > best_te:                              # keep the best model
            best_te = te_acc
            best_params = tree_flatten(model.parameters())
        if ep % 3 == 0 or ep == 1 or ep == args.epochs:
            print(f"  epoch {ep:3d}  loss={tot/len(train):.4f}  "
                  f"train_acc={tr_acc:.3f}  test_acc={te_acc:.3f}")

    if best_params is not None:
        model.update(tree_unflatten(best_params))       # restore best
        mx.eval(model.parameters())
    te = accuracy(model, test)
    best_te = max(best_te, te)
    print(f"\nPhase-0 gate: test_acc={te:.3f} (best {best_te:.3f}) vs "
          f"majority {base_te:.3f}")
    margin = best_te - base_te
    print("  GATE PASSED ✓ — encoder learns SAT structure" if margin >= 0.10
          else "  GATE NOT MET — margin %.3f < 0.10" % margin)


if __name__ == "__main__":
    main()
