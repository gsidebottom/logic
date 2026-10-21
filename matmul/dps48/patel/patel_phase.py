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
import rebuild3  # noqa: E402


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
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    prog = slp.parse_slp(a.slp)
    target = slp.eval_map(prog, a.n)
    start = time.monotonic()
    search = rebuild3.Search(prog, a.n, a.seed, a.orders, a.temperature, a.tabu, rebuild3.DEFAULT_WEIGHTS)
    assert slp.eval_map(search.best_prog, a.n) == target, "seed rebuild changed the map"
    before = slp.count_ops(prog)["total"]
    print(f"start: {before} ops (his model) -> rebuilt {search.best_cost}; {len(target)} outputs, {a.n} inputs, seed {a.seed}", flush=True)
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
    print(f"final: best {search.best_cost} ops (his model) after {search.stats['iterations']} iterations -> {a.out}/best.slp", flush=True)


if __name__ == "__main__":
    main()
