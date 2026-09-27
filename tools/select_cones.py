#!/usr/bin/env python3
"""Select the cones worth keeping as tables: those whose GAC over the cone's
function forces, on the cone's interface, what unit propagation over the
cone's own gate clauses does not.

    tools/select_cones.py DIR --threshold 0.15 [--samples 400] --out DIR_sel

DIR is a cnf2boxes.py output (boxes.json, cones.json, tables/, residual.cnf).
Each cone is scored as tools/mine_boxes.py scores a candidate group -- random
partial assignments, but here over the cone's INTERFACE variables (inputs and
visible outputs; the hidden ones are what the search never sees), counting
the extra interface literals GAC forces and the conflicts it sees that UP
misses.  Cones sharing a table share a score.  The output has the selected
instances (boxes.json) and residual.cnf = DIR's residual plus the clauses of
every cone NOT selected, so residual + boxes is again the whole formula.
"""
import argparse, json, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mine_boxes import masks, up_closure

def score_cone(rec, table, samples, rng):
    """GAC over the cone's PROJECTED table (rows over inputs + visible outputs,
    None = don't care) against unit propagation over the cone's clauses
    (hidden variables included), compared on the interface."""
    vs = sorted({abs(l) for c in rec["clauses"] for l in c})
    n = len(vs)
    index = {v: i for i, v in enumerate(vs)}
    ms = masks(rec["clauses"], index)
    iface_vars = rec["inputs"] + rec["visible"]
    iface = [index[v] for v in iface_vars]
    iface_mask = sum(1 << i for i in iface)
    # each row as (specified mask, value mask) over local indices
    rows = []
    for r in table["rows"]:
        spec = val = 0
        for col, x in zip(iface, r):
            if x is None: continue
            spec |= 1 << col
            if x: val |= 1 << col
        rows.append((spec, val))
    extra, extra_conf, wins = 0, 0, 0
    for _ in range(samples):
        k = rng.randrange(1, max(2, len(iface) // 2 + 1))
        asg = val = 0
        for i in rng.sample(iface, k):
            asg |= 1 << i
            if rng.random() < 0.5: val |= 1 << i
        ua, uv, uc = up_closure(ms, n, asg, val)
        live = [(sp, vl) for sp, vl in rows if (asg & sp & (val ^ vl)) == 0]
        if not live:
            if not uc: extra_conf += 1; wins += 1
            continue
        if uc: continue
        forced = iface_mask
        ones = iface_mask
        for sp, vl in live:
            forced &= sp
            ones &= vl | ~sp
        # forced: specified in every live row with one value throughout
        zeros = iface_mask
        for sp, vl in live: zeros &= ~vl | ~sp
        ga = (forced & ones) | (forced & zeros)
        d = bin(ga & ~ua & iface_mask).count("1")
        if d: extra += d; wins += 1
    return dict(n=n, rows=len(rows), iface=len(iface), extra=extra / samples, extra_conf=extra_conf / samples, wins=wins / samples)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dir"); ap.add_argument("--threshold", type=float, default=0.15, help="keep cones whose table wins on at least this share of samples")
    ap.add_argument("--samples", type=int, default=400); ap.add_argument("--out", required=True); ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    insts = json.load(open(os.path.join(args.dir, "boxes.json")))
    cones = json.load(open(os.path.join(args.dir, "cones.json")))
    rng = random.Random(args.seed)
    by_table = {}
    scored = []
    for rec in cones:
        t = insts[rec["instance"]]["table"]
        if t not in by_table:
            table = json.load(open(os.path.join(args.dir, t)))
            by_table[t] = score_cone(rec, table, args.samples, rng)
        scored.append((rec, by_table[t]))
    keep = [rec["instance"] for rec, sc in scored if sc is not None and sc["wins"] >= args.threshold]
    keep_set = set(keep)
    os.makedirs(args.out, exist_ok=True)
    # tables are referenced relatively: point at DIR's
    rel = os.path.relpath(os.path.join(args.dir, "tables"), args.out)
    sel = [dict(insts[i], table=os.path.join(rel, os.path.basename(insts[i]["table"]))) for i in keep]
    json.dump(sel, open(os.path.join(args.out, "boxes.json"), "w"))
    restored = [c for rec, sc in scored if rec["instance"] not in keep_set for c in rec["clauses"]]
    with open(os.path.join(args.dir, "residual.cnf")) as f:
        header = f.readline().split(); rest = f.read()
    nv, nc = int(header[2]), int(header[3])
    with open(os.path.join(args.out, "residual.cnf"), "w") as out:
        out.write(f"p cnf {nv} {nc + len(restored)}\n"); out.write(rest)
        for c in restored: out.write(" ".join(map(str, c)) + " 0\n")
    summary = dict(cones=len(cones), tables=len(by_table), kept=len(keep), threshold=args.threshold, restored_clauses=len(restored),
                   unscored=sum(1 for _, sc in scored if sc is None),
                   tables_scored=sorted(((t, round(sc["wins"], 3), round(sc["extra"], 3), sc["n"], sc["rows"]) for t, sc in by_table.items() if sc), key=lambda x: -x[1]))
    json.dump(summary, open(os.path.join(args.out, "selection.json"), "w"), indent=1)
    print(f"{args.dir}: {len(cones)} cones over {len(by_table)} tables; kept {len(keep)} at wins >= {args.threshold} ({len(restored)} clauses restored, {summary['unscored']} unscored)")
    for t, w, e, n, r in summary["tables_scored"][:12]: print(f"   {t:18s} wins {w:5.3f}  extra {e:5.3f}  n {n:2d}  rows {r}")

if __name__ == "__main__":
    main()
