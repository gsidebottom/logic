#!/usr/bin/env python3
"""Write the single-move orbit neighbourhood of a rank-48 point as a pool for
sweep.py: every neighbour under one elementary isotropy move (GL shears and
dyadic diagonal scalings on X, Y, Z; per-product (a, b, 1/ab) rescalings),
deduplicated by orbit48.point_key, with proxy objective <= --max-obj, as
OUTDIR/nbrNNN_{L,R,P}.sms plus OUTDIR/candidates.csv (orbit48 format).

Usage: neighbours48.py PREFIX OUTDIR [--lam 0.3] [--max-obj 180] [--depth 1]
Runs under the system python3 (numpy).
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)
import orbit48 as O  # noqa: E402
from orbitclimb48 import neighbours  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("prefix")
    ap.add_argument("outdir")
    ap.add_argument("--lam", type=float, default=0.3)
    ap.add_argument("--max-obj", type=float, default=180.0)
    ap.add_argument("--depth", type=int, default=1, help="moves composed (depth 2 = neighbours of neighbours, proxy-filtered)")
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)
    U, V, W = O.load(a.prefix)
    assert O.brent_ok(U, V, W)
    seen = {O.point_key(U, V, W)}
    frontier = [(U, V, W)]
    found = []
    for d in range(a.depth):
        nxt = []
        for mats in frontier:
            for desc, new in neighbours(*mats):
                k = O.point_key(*new)
                if k in seen:
                    continue
                seen.add(k)
                obj, floor, sides, nonu = O.objective(*new, a.lam)
                if obj <= a.max_obj:
                    found.append((obj, floor, sides, nonu, f"d{d + 1} {desc}", new))
                    nxt.append(new)
        frontier = nxt
        print(f"depth {d + 1}: {len(found)} neighbours kept so far ({len(seen) - 1} distinct seen)", flush=True)
    found.sort(key=lambda t: (t[0], t[1]))
    rows = ["rank,floor,fl,fr,fp,nonunit,objective,prefix"]
    for n, (obj, floor, sides, nonu, desc, new) in enumerate(found):
        assert O.brent_ok(*new)
        pre = os.path.join(a.outdir, f"nbr{n:03d}")
        O.write_sms(pre, *new)
        rows.append(f"{n},{floor},{sides[0]},{sides[1]},{sides[2]},{nonu},{obj:.1f},{pre}")
        open(pre + ".move", "w").write(desc + "\n")
    open(os.path.join(a.outdir, "candidates.csv"), "w").write("\n".join(rows) + "\n")
    print(f"wrote {len(found)} neighbours with proxy <= {a.max_obj} to {a.outdir}/candidates.csv")


if __name__ == "__main__":
    main()
