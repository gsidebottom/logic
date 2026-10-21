#!/opt/homebrew/bin/python3
"""Run Patel's phase LNS (rebuild2.Search, CC0, rp440/matmul-4x4-48-202) on ONE
linear map given as a PLinOpt-syntax program, outside his triple admission --
for the transpose P^T (48 x 16) of a rank-48 scheme's output map, whose program
is transposed back afterwards (Tellegen: +32 additions).  The map is checked
to be unchanged after every accepted move and at the end; everything written
is re-verified independently downstream (slp48check.py, SLPchecker).

Usage: patel_phase.py --slp PROG.slp --n 16 --seed S --wall SECONDS --out DIR
"""
import argparse
import json
import os
import sys
import time

SEARCH = os.environ.get("PATEL_SEARCH", os.path.expanduser("~/src/matmul-4x4-48-202/search"))  # clone of rp440/matmul-4x4-48-202
sys.path.insert(0, SEARCH)
import slp  # noqa: E402
import rebuild  # noqa: E402
import rebuild2  # noqa: E402
import rebuild3  # noqa: E402


def plinopt_count(prog):
    """PLinOpt's count: additions + scalings; negations and copies are free."""
    c = slp.count_ops(prog)
    return c["adds"] + c["scalings"]


class PlinoptCatalog(rebuild2.Catalog):
    """His catalog with PLinOpt's objective: the cost of a value set is the
    number of produced values (negations are free), and the signs come from
    his greedy plan instead of the z3 planner (72% of the step time in a
    profile, 2026-10-21), which only minimizes paid negations."""

    def plan(self, selected):
        return self.prune(selected, rebuild.Catalog.plan(self, selected))[1]

    def prune(self, selected, plan):
        live, (cost, chosen, signs, fixes) = super().prune(selected, plan)
        return live, (len(chosen), chosen, signs, fixes)

    def emit(self, selected, plan=None):
        # his emitter asserts its own recount (negations charged) against the plan's cost
        cost, chosen, signs, fixes = plan or self.plan(selected)
        return super().emit(selected, (len(chosen) + len(fixes), chosen, signs, fixes))


def use_plinopt_model():
    rebuild2.Catalog = PlinoptCatalog  # Search, Proposals and reverse_delete look the name up at call time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--slp", required=True)
    ap.add_argument("--n", type=int, default=16, help="number of inputs")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--wall", type=float, default=600)
    ap.add_argument("--out", required=True)
    ap.add_argument("--orders", type=int, default=4)
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--tabu", type=int, default=256)
    ap.add_argument("--log-seconds", type=float, default=60)
    ap.add_argument("--plinopt-model", action="store_true", help="PLinOpt's objective (negations free), greedy signs, no z3")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    if a.plinopt_model:
        use_plinopt_model()
    prog = slp.parse_slp(a.slp)
    target = slp.eval_map(prog, a.n)
    start = time.monotonic()
    search = rebuild3.Search(prog, a.n, a.seed, a.orders, a.temperature, a.tabu, rebuild3.DEFAULT_WEIGHTS)
    assert slp.eval_map(search.best_prog, a.n) == target, "seed rebuild changed the map"
    model = "PLinOpt" if a.plinopt_model else "his"
    if a.plinopt_model:
        # his constructor prices the seed in his model; re-price it in ours
        search.current_cost = search.best_cost = plinopt_count(search.best_prog)
    before = slp.count_ops(prog)["total"] if not a.plinopt_model else plinopt_count(prog)
    print(f"start: {before} ops ({model} model) -> rebuilt {search.best_cost}; {len(target)} outputs, {a.n} inputs, seed {a.seed}", flush=True)
    saved = None
    next_log = a.log_seconds
    while time.monotonic() - start < a.wall:
        move = search.step()
        if move:
            assert slp.eval_map(search.current_prog, a.n) == target, "accepted move changed the map"
        if saved is None or search.best_cost < saved:
            assert slp.eval_map(search.best_prog, a.n) == target
            rebuild3.write_slp(os.path.join(a.out, "best.slp"), search.best_prog)
            saved = search.best_cost
            print(f"  {time.monotonic() - start:7.1f}s  best {saved}  (iteration {search.stats['iterations']})", flush=True)
        el = time.monotonic() - start
        if el >= next_log:
            print(f"progress {el:.0f}s: best {search.best_cost} current {search.current_cost} iterations {search.stats['iterations']} plateau {search.stats.get('plateau_moves', 0)} annealing {search.stats.get('annealing_moves', 0)}", flush=True)
            next_log = el + a.log_seconds
    assert slp.eval_map(search.best_prog, a.n) == target
    rebuild3.write_slp(os.path.join(a.out, "best.slp"), search.best_prog)
    summary = dict(seed=a.seed, before=before, best=search.best_cost, iterations=search.stats["iterations"],
                   wall=time.monotonic() - start, stats=dict(search.stats))
    json.dump(summary, open(os.path.join(a.out, "summary.json"), "w"), indent=1)
    print(f"final: best {search.best_cost} ops ({model} model) after {search.stats['iterations']} iterations -> {a.out}/best.slp", flush=True)


if __name__ == "__main__":
    main()
