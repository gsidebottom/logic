#!/usr/bin/env python3
"""Random-walk samples of a rank-48 point's orbit, NOT optimized for the proxy:
from PREFIX, apply --depth random elementary isotropy moves (GL shears with
c in +-1, +-1/2, +-2 and dyadic diagonal scalings on X, Y, Z, plus
per-product (a, b, 1/ab) rescalings), keeping only moves whose result stays
within orbit48's entry range; record the end point of each walk (and the
point at --record-every steps) with its proxy, deduplicated by point_key, as
an orbit48-format pool (OUTDIR/smpNNN_{L,R,P}.sms + candidates.csv) for
sweep.py.  Shows whether regions the proxy does not favour are competitive.

Usage: orbitsample48.py PREFIX OUTDIR [--walks 40] [--depth 12] [--record-every 4]
       [--seed 1] [--lam 0.3] [--max-floor 0]
Runs under the system python3 (numpy).
"""
import argparse
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)
import orbit48 as O  # noqa: E402
from orbitclimb48 import PRODUCT_SCALES, scale_rows  # noqa: E402

SCAL = O.SCAL


def random_move(mats, rng):
    """one random elementary move; returns (description, new mats) or None."""
    U, V, W = mats
    I = O.ident()
    if rng.random() < 0.6:
        f = rng.randrange(3)
        kind = rng.choice(["add", "add", "add", "scale2", "scaleh"])
        i, j = rng.randrange(4), rng.randrange(4)
        if kind == "add" and i == j:
            return None
        c = rng.choice([SCAL, -SCAL, SCAL // 2, -SCAL // 2, 2 * SCAL, -2 * SCAL]) if kind == "add" else 0
        E, Ei = O.elementary(kind, i, j, c)
        ms = [I, I, I, I, I, I]
        ms[2 * f], ms[2 * f + 1] = E, Ei
        new = O.apply(U, V, W, *ms)
        desc = f"{'XYZ'[f]} {kind} {i} {j} {c // SCAL if kind == 'add' and abs(c) >= SCAL else (c / SCAL if kind == 'add' else '')}"
    else:
        k = rng.randrange(U.shape[0])
        a, b = rng.choice(PRODUCT_SCALES)
        U2, V2 = scale_rows(U, k, a), scale_rows(V, k, b)
        from fractions import Fraction as Fr
        W2 = scale_rows(W, k, 1 / (Fr(a) * Fr(b)))
        if U2 is None or V2 is None or W2 is None:
            return None
        new = (U2, V2, W2)
        desc = f"product {k} x({a},{b})"
    if new is None or not O.in_range(*new):
        return None
    return desc, new


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("prefix")
    ap.add_argument("outdir")
    ap.add_argument("--walks", type=int, default=40)
    ap.add_argument("--depth", type=int, default=12)
    ap.add_argument("--record-every", type=int, default=4)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--lam", type=float, default=0.3)
    ap.add_argument("--max-floor", type=int, default=0, help="drop points with a larger floor (0 = keep all)")
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)
    rng = random.Random(a.seed)
    U, V, W = O.load(a.prefix)
    assert O.brent_ok(U, V, W)
    seen = {O.point_key(U, V, W)}
    found = []
    tries = 0
    for wk in range(a.walks):
        mats = (U, V, W)
        path = []
        step = 0
        while step < a.depth and tries < 100000:
            tries += 1
            mv = random_move(mats, rng)
            if mv is None:
                continue
            desc, mats = mv
            path.append(desc)
            step += 1
            if step % a.record_every == 0 or step == a.depth:
                k = O.point_key(*mats)
                if k in seen:
                    continue
                seen.add(k)
                obj, floor, sides, nonu = O.objective(*mats, a.lam)
                if a.max_floor and floor > a.max_floor:
                    continue
                found.append((obj, floor, sides, nonu, f"walk {wk} step {step}: " + " | ".join(path), mats))
    found.sort(key=lambda t: (t[0], t[1]))
    rows = ["rank,floor,fl,fr,fp,nonunit,objective,prefix"]
    for n, (obj, floor, sides, nonu, desc, mats) in enumerate(found):
        assert O.brent_ok(*mats)
        pre = os.path.join(a.outdir, f"smp{n:03d}")
        O.write_sms(pre, *mats)
        rows.append(f"{n},{floor},{sides[0]},{sides[1]},{sides[2]},{nonu},{obj:.1f},{pre}")
        open(pre + ".moves", "w").write(desc + "\n")
    open(os.path.join(a.outdir, "candidates.csv"), "w").write("\n".join(rows) + "\n")
    floors = sorted(f[1] for f in found)
    print(f"wrote {len(found)} sampled points to {a.outdir}/candidates.csv; floors {floors[0]}..{floors[-1]} (median {floors[len(floors) // 2]}); proxy {found[0][0]:.1f}..{found[-1][0]:.1f}")


if __name__ == "__main__":
    main()
