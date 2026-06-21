#!/usr/bin/env python3
"""
GNN cut-scorer over the GMI constraint graph — de-risking the "richer
representation" question before the full expert-iteration build.

The hand-feature logistic (cp_gmi_policy) already gives ~5.3× fewer cuts and
pushes the ceiling.  Does a GNN that *sees the constraint graph* (Gasse et al.
2019, learned MILP cut/branch selection) predict cut-usefulness BETTER than the 9
intrinsic features?  If yes → representation is a lever (worth a Rust-inference
port + expert iteration); if comparable → hand-features suffice and the lever is
search (expert iteration), not representation.  Either way the answer is the
gate.

Graph (bipartite, à la Gasse): variable nodes [x*_v, fractionality] and
constraint nodes [rhs, slack@x*, is-candidate]; edges carry the coefficient.
A few message-passing rounds, then a per-candidate-cut readout → P(useful).
Imitation labels = the transitive Farkas support (same as the logistic).

Usage:  cp_gmi_gnn.py [--train 4_3 5_4] [--test 6_5] [--seeds 3]
"""
from __future__ import annotations
import argparse, math, os, sys, tempfile, time
import numpy as np
import mlx.core as mx
import mlx.nn as nn
import mlx.optimizers as optim
from mlx.utils import tree_map

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cp_search as cp                                    # noqa: E402
import cp_lp                                              # noqa: E402
import cp_gmi                                             # noqa: E402
import cp_gmi_policy as pol                               # noqa: E402
import cp_sweep                                           # noqa: E402
from cp_policy import logreg_fit, standardize            # noqa: E402

TD = tempfile.mkdtemp(prefix="gmignn_")


def cnf_for(tag):
    P, H = tag.split("_")
    path = os.path.join(TD, f"php_{tag}.cnf")
    if not os.path.exists(path):
        cp_gmi.php_cnf(int(P), int(H), path)
    return path


# ── data: per-(round,objective) snapshots labeled by the Farkas support ──────

def record(path, seed=0, n_obj=4, max_rounds=120, max_secs=120):
    """Add-all GMI run; capture (cons_so_far, x*, [candidate cuts]) per vertex,
    then label each candidate by the transitive Farkas support of the refutation.
    Returns [(cons, x_float, [(cut, label)])] or None."""
    inputs = cp.read_cnf(path)
    nvars = max(v for c in inputs for v in c.coef)
    cons = list(inputs)
    seen = {c.canonical().key() for c in cons}
    recipes, snaps = [], []
    rng = np.random.default_rng(seed)
    t0 = time.time()
    refuted = False
    for _ in range(max_rounds):
        if time.time() - t0 > max_secs:
            break
        progressed = False
        objs = [None] + [list(rng.uniform(-1, 1, nvars)) for _ in range(n_obj - 1)]
        for obj in objs:
            std = cp_gmi.Standard(cons, nvars)
            status, T, b, basis = cp_gmi.solve(std, obj)
            if status == "infeasible":
                refuted = True
                break
            x = cp_gmi.primal(std, b, basis)
            newc = []
            for viol, cut, recipe in cp_gmi.gomory_cuts(std, T, b, basis, x):
                k = cut.canonical().key()
                if k not in seen:
                    seen.add(k)
                    newc.append((cut, recipe))
            if newc:
                progressed = True
                base = len(cons)
                snaps.append((list(cons), [float(xi) for xi in x],
                              [(cut, base + i) for i, (cut, _) in enumerate(newc)]))
                for cut, recipe in newc:
                    recipes.append(recipe); cons.append(cut)
        if refuted:
            break
        if not progressed:
            break
    if not refuted:
        return None
    mult = cp_lp.farkas_refute(cons)
    if not mult:
        return None
    useful = pol.compute_useful(len(inputs), recipes, mult)
    out = []
    for snap_cons, x, cands in snaps:
        out.append((snap_cons, x, [(cut, 1.0 if ci in useful else 0.0)
                                   for cut, ci in cands]))
    ncand = sum(len(c) for _, _, c in out)
    npos = sum(int(l) for _, _, c in out for _, l in c)
    print(f"  record {os.path.basename(path)} seed{seed}: {len(out)} snapshots, "
          f"{ncand} candidates, {npos} useful ({npos / max(1, ncand):.0%})")
    return out


def build_graph(snap_cons, x, cands, nvars):
    """Bipartite var×constraint graph as dense MLX arrays.  Constraint nodes =
    existing cons followed by candidate cuts."""
    pbs = list(snap_cons) + [cut for cut, _ in cands]
    C = len(pbs)
    M = np.zeros((C, nvars), dtype=np.float32)
    cfeat = np.zeros((C, 3), dtype=np.float32)
    for c, pb in enumerate(pbs):
        absum = 1.0 + sum(abs(a) for a in pb.coef.values())
        slack = sum(a * x[v - 1] for v, a in pb.coef.items()) - pb.rhs
        for v, a in pb.coef.items():
            M[c, v - 1] = a
        cfeat[c] = [pb.rhs / absum, slack / absum,
                    1.0 if c >= len(snap_cons) else 0.0]
    vfeat = np.zeros((nvars, 2), dtype=np.float32)
    for v in range(nvars):
        xv = x[v]
        vfeat[v] = [xv, min(xv, 1.0 - xv)]
    cand_idx = list(range(len(snap_cons), C))
    labels = [lab for _, lab in cands]
    return {
        "M": mx.array(M), "Mt": mx.array(M.T),
        "vfeat": mx.array(vfeat), "cfeat": mx.array(cfeat),
        "cand_idx": mx.array(np.array(cand_idx, dtype=np.int32)),
        "labels": mx.array(np.array(labels, dtype=np.float32)),
    }


# ── model ────────────────────────────────────────────────────────────────────

class CutGNN(nn.Module):
    def __init__(self, dim=32, rounds=8):
        super().__init__()
        self.rounds = rounds
        self.v_emb = nn.Linear(2, dim)
        self.c_emb = nn.Linear(3, dim)
        self.v2c = nn.Linear(dim, dim)
        self.c2v = nn.Linear(dim, dim)
        self.c_upd = nn.Linear(2 * dim, dim)
        self.v_upd = nn.Linear(2 * dim, dim)
        self.ln_c = nn.LayerNorm(dim)
        self.ln_v = nn.LayerNorm(dim)
        self.readout = nn.Sequential(nn.Linear(dim, dim), nn.ReLU(), nn.Linear(dim, 1))

    def __call__(self, g):
        V = self.v_emb(g["vfeat"])
        C = self.c_emb(g["cfeat"])
        for _ in range(self.rounds):
            c_msg = g["M"] @ self.v2c(V)
            C = self.ln_c(C + mx.tanh(self.c_upd(mx.concatenate([C, c_msg], axis=-1))))
            v_msg = g["Mt"] @ self.c2v(C)
            V = self.ln_v(V + mx.tanh(self.v_upd(mx.concatenate([V, v_msg], axis=-1))))
        logits = self.readout(C).reshape(-1)
        return mx.take(logits, g["cand_idx"])


def loss_fn(model, g):
    return nn.losses.binary_cross_entropy(model(g), g["labels"], with_logits=True)


# ── train + A/B vs logistic ──────────────────────────────────────────────────

def gather(paths, seeds):
    data = []
    for path in paths:
        for s in range(seeds):
            r = record(path, seed=s)
            if r:
                data.extend(r)
    return data


def to_graphs(data, nvars):
    return [build_graph(c, x, cands, nvars) for c, x, cands in data if cands]


def gnn_acc(model, graphs):
    tp = tot = 0
    for g in graphs:
        p = (mx.sigmoid(model(g)) >= 0.5).astype(mx.int32)
        y = (g["labels"] >= 0.5).astype(mx.int32)
        tp += int(mx.sum(p == y).item()); tot += int(g["labels"].shape[0])
    return tp / max(1, tot)


def logistic_ab(train_data, test_data, nvars):
    """Same labels/split, 9 hand-features → held-out accuracy (the baseline)."""
    def feats(data):
        X, y = [], []
        for cons, x, cands in data:
            for cut, lab in cands:
                # viol@x and a recipe-free feature proxy (intrinsic cut features)
                viol = cut.rhs - sum(a * x[v - 1] for v, a in cut.coef.items())
                coefs = [abs(a) for a in cut.coef.values()]
                X.append([float(viol), 0.0, 0.0, 0.0, 0.0, float(abs(cut.rhs)),
                          float(len(cut.coef)), float(max(coefs) if coefs else 0),
                          len(cut.coef) / max(1, nvars)])
                y.append(lab)
        return np.array(X), np.array(y)
    Xtr, ytr = feats(train_data); Xte, yte = feats(test_data)
    mu, sd = standardize(Xtr)
    Ztr = np.clip((Xtr - mu) / sd, -10, 10); Zte = np.clip((Xte - mu) / sd, -10, 10)
    w, b = logreg_fit(Ztr, ytr)
    pred = (1.0 / (1.0 + np.exp(-np.clip(Zte @ w + b, -30, 30))) >= 0.5)
    return float((pred == (yte >= 0.5)).mean())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--train", nargs="*", default=["4_3", "5_4"])
    ap.add_argument("--test", nargs="*", default=["6_5"])
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--dim", type=int, default=32)
    ap.add_argument("--rounds", type=int, default=8)
    ap.add_argument("--epochs", type=int, default=120)
    ap.add_argument("--lr", type=float, default=3e-3)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--gphp", nargs=5, metavar=("P", "H", "DENS", "NTRAIN", "NTEST"),
                    help="graph-PHP testbed: generate NTRAIN train + NTEST held-out instances")
    args = ap.parse_args()
    mx.random.seed(args.seed)

    if args.gphp:
        P, H, dens = int(args.gphp[0]), int(args.gphp[1]), float(args.gphp[2])
        ntr, nte = int(args.gphp[3]), int(args.gphp[4])
        train_paths = [cp_sweep.graph_php_cnf(P, H, dens, s, os.path.join(TD, f"g_{s}.cnf"))
                       for s in range(ntr)]
        test_paths = [cp_sweep.graph_php_cnf(P, H, dens, 1000 + s, os.path.join(TD, f"gte_{s}.cnf"))
                      for s in range(nte)]
        nvars_ref = P * H
        seeds = 1                                          # instances already vary
    else:
        train_paths = [cnf_for(t) for t in args.train]
        test_paths = [cnf_for(t) for t in args.test]
        nvars_ref = max(int(t.split("_")[0]) * int(t.split("_")[1])
                        for t in args.train + args.test)
        seeds = args.seeds
    print("=== record train ==="); train_data = gather(train_paths, seeds)
    print("=== record test  ==="); test_data = gather(test_paths, 1)
    # one graph per snapshot; pad var dim to the max so M shapes are consistent? No —
    # each graph is independent (its own nvars from its instance).  Use per-graph nvars.
    def nvars_of(tag_data):
        return max((v for cons, _, _ in tag_data for c in cons for v in c.coef),
                   default=1)
    # graphs carry their own instance nvars
    tr_graphs, te_graphs = [], []
    for cons, x, cands in train_data:
        if cands:
            nv = max(v for c in cons for v in c.coef)
            tr_graphs.append(build_graph(cons, x, cands, nv))
    for cons, x, cands in test_data:
        if cands:
            nv = max(v for c in cons for v in c.coef)
            te_graphs.append(build_graph(cons, x, cands, nv))
    ntr = sum(g["labels"].shape[0] for g in tr_graphs)
    nte = sum(g["labels"].shape[0] for g in te_graphs)
    base_te = max(
        sum(int(mx.sum(g["labels"]).item()) for g in te_graphs),
        nte - sum(int(mx.sum(g["labels"]).item()) for g in te_graphs)) / max(1, nte)
    print(f"train graphs={len(tr_graphs)} ({ntr} cands)  "
          f"test graphs={len(te_graphs)} ({nte} cands)  "
          f"majority baseline(test)={base_te:.3f}")
    if not tr_graphs or not te_graphs:
        print("  ABORT: no data recorded (instances not refuted in time — "
              "use smaller instances or longer --max-secs)")
        return

    model = CutGNN(args.dim, args.rounds)
    mx.eval(model.parameters())
    opt = optim.Adam(learning_rate=args.lr)
    lag = nn.value_and_grad(model, loss_fn)
    best_te, best = 0.0, None
    for ep in range(1, args.epochs + 1):
        acc = None
        for g in tr_graphs:
            _, grads = lag(model, g)
            acc = grads if acc is None else tree_map(lambda a, b: a + b, acc, grads)
        acc = tree_map(lambda a: a * (1.0 / max(1, len(tr_graphs))), acc)
        acc, _ = optim.clip_grad_norm(acc, 5.0)
        opt.update(model, acc)
        mx.eval(model.parameters(), opt.state)
        if ep % 20 == 0 or ep == args.epochs:
            tr_a, te_a = gnn_acc(model, tr_graphs), gnn_acc(model, te_graphs)
            print(f"  ep{ep}: train_acc={tr_a:.3f}  test_acc={te_a:.3f}")
            if te_a > best_te:
                best_te = te_a

    log_te = logistic_ab(train_data, test_data, nvars_ref)
    print(f"\n=== A/B (held-out cut-usefulness accuracy) ===")
    print(f"  majority baseline : {base_te:.3f}")
    print(f"  logistic (9 feats): {log_te:.3f}")
    print(f"  GNN (graph)       : {best_te:.3f}")


if __name__ == "__main__":
    main()
