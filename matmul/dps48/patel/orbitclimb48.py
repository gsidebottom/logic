#!/usr/bin/env python3
"""True-cost hill climb over single orbit moves of a rank-48 point.

Runs under the system python3 (needs numpy for orbit48); the LNS itself runs
in subprocesses under sweep.PY (Homebrew python3.14 with z3).

From a point (PREFIX_{L,R,P}.sms over Z[1/2]) enumerate its neighbours under
one elementary isotropy move -- GL(4) shears row_i += c row_j (c in +-1,
+-1/2, +-2) and dyadic diagonal scalings on each of the three axes, and
per-product rescalings (L_k, R_k, P_k) -> (a L_k, b R_k, P_k / ab) with
a, b in {1, 2, 1/2} -- keep the --keep best by the orbit48 proxy (floor +
lam * non-unit coefficients), and evaluate each kept neighbour's TRUE cost
with Patel's LNS at a fixed budget per side (L, R directly, P through its
transpose; PLinOpt counts via SLPchecker).  Accept the cheapest neighbour
when it beats the incumbent evaluated at the same budget; repeat.  The final
point is written with its programs to OUTDIR/best.

Usage: orbitclimb48.py PREFIX OUTDIR [--procs 12] [--seconds 60] [--keep 48]
       [--steps 4] [--lam 0.3] [--seed 1] [--final-seconds 600]
"""
import argparse
import csv
import os
import shutil
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as Fr

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)
import orbit48 as O  # noqa: E402
import sweep as S  # noqa: E402

SCAL = O.SCAL
PRODUCT_SCALES = [(2, 1), (Fr(1, 2), 1), (1, 2), (1, Fr(1, 2)), (2, Fr(1, 2)), (Fr(1, 2), 2)]


def scale_rows(M, k, c):
    """row k of a (r, 4, 4) numerator array times c, or None if not representable."""
    c = Fr(c)
    row = M[k].astype(object) * c.numerator
    if c.denominator != 1 and (np.array([int(x) % c.denominator for x in row.flat]) != 0).any():
        return None
    out = M.copy()
    out[k] = np.array([int(x) // c.denominator for x in row.flat], dtype=np.int64).reshape(4, 4)
    return out


def neighbours(U, V, W):
    """yield (description, (U', V', W')) for every single move."""
    I = O.ident()
    for f, axis in enumerate("XYZ"):
        moves = [("add", i, j, c) for i in range(4) for j in range(4) if i != j
                 for c in (SCAL, -SCAL, SCAL // 2, -SCAL // 2, 2 * SCAL, -2 * SCAL)]
        moves += [(kind, i, i, 0) for i in range(4) for kind in ("scale2", "scaleh")]
        for kind, i, j, c in moves:
            E, Ei = O.elementary(kind, i, j, c)
            mats = [I, I, I, I, I, I]
            mats[2 * f], mats[2 * f + 1] = E, Ei
            new = O.apply(U, V, W, *mats)
            if new is not None and O.in_range(*new):
                yield (f"{axis} {kind} {i} {j} {Fr(c, SCAL) if kind == 'add' else ''}".strip(), new)
    r = U.shape[0]
    for k in range(r):
        for a, b in PRODUCT_SCALES:
            U2 = scale_rows(U, k, a)
            V2 = scale_rows(V, k, b)
            W2 = scale_rows(W, k, 1 / (Fr(a) * Fr(b)))
            if U2 is None or V2 is None or W2 is None:
                continue
            new = (U2, V2, W2)
            if O.in_range(*new):
                yield (f"product {k} x({a},{b})", new)


class Point:
    def __init__(self, tag, mats, workdir):
        self.tag, self.mats = tag, mats
        self.dir = os.path.join(workdir, tag)
        os.makedirs(self.dir, exist_ok=True)
        self.prefix = os.path.join(self.dir, "pt")
        O.write_sms(self.prefix, *mats)
        self.sms = {s: f"{self.prefix}_{s}.sms" for s in "LRP"}
        self.sms["Pt"] = os.path.join(self.dir, "Pt.sms")
        self.seed_prog, self.cost = {}, {}
        self.ok = True

    def stage(self):
        """PLinOpt seeds: L and R directly, P^T from the transposed matrix."""
        _, t = S.run([f"{S.BIN}/matrix-transpose", self.sms["P"]])
        open(self.sms["Pt"], "w").write(t)
        for side in ("L", "R", "Pt"):
            best = None
            for _ in range(2):
                _, o = S.run([f"{S.BIN}/optimizer", "-O", "50", self.sms[side]], timeout=900)
                o = S.strip(o)
                c = S.slpcheck(self.sms[side], o)
                if c and (best is None or sum(c) < best[0]):
                    best = (sum(c), o)
            if best is None:
                self.ok = False
                return
            dst = os.path.join(self.dir, f"seed_{side}.slp")
            open(dst, "w").write(best[1])
            self.seed_prog[side] = dst
            self.cost[side] = best[0] + (32 if side == "Pt" else 0)

    def total(self):
        return self.cost["L"] + self.cost["R"] + self.cost["Pt"]


def evaluate(points, seconds, seed, pool, label):
    jobs = [(p, s) for p in points for s in ("L", "R", "Pt")]

    def one(j):
        p, s = j
        return S.job(p, s, seed, seconds, label)

    for p, side, cost, best in pool.map(one, jobs):
        if cost is not None and cost < p.cost[side]:
            p.cost[side], p.seed_prog[side] = cost, best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("prefix")
    ap.add_argument("outdir")
    ap.add_argument("--procs", type=int, default=12)
    ap.add_argument("--seconds", type=float, default=60)
    ap.add_argument("--keep", type=int, default=48)
    ap.add_argument("--steps", type=int, default=4)
    ap.add_argument("--lam", type=float, default=0.3)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--final-seconds", type=float, default=600)
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)
    U, V, W = O.load(a.prefix)
    assert O.brent_ok(U, V, W), "input fails Brent"
    seen = {O.point_key(U, V, W)}
    log = open(os.path.join(a.outdir, "climb.log"), "a")

    def say(msg):
        print(msg, flush=True)
        log.write(msg + "\n")
        log.flush()

    with ThreadPoolExecutor(a.procs) as pool:
        inc = Point("step0_incumbent", (U, V, W), a.outdir)
        inc.stage()
        assert inc.ok
        evaluate([inc], a.seconds, a.seed, pool, "eval")
        say(f"incumbent {a.prefix}: proxy {O.objective(U, V, W, a.lam)[1:]} true@{a.seconds:.0f}s {inc.total()} = {inc.cost}")
        for step in range(1, a.steps + 1):
            t0 = time.time()
            cands = []
            for desc, new in neighbours(*inc.mats):
                k = O.point_key(*new)
                if k in seen:
                    continue
                seen.add(k)
                obj, floor, sides, nonu = O.objective(*new, a.lam)
                cands.append((obj, floor, sides, nonu, desc, new))
            cands.sort(key=lambda c: (c[0], c[1]))
            say(f"step {step}: {len(cands)} new neighbours; proxy range {cands[0][0]:.1f} .. {cands[-1][0]:.1f}; evaluating the best {a.keep}")
            pts = []
            for n, (obj, floor, sides, nonu, desc, new) in enumerate(cands[:a.keep]):
                p = Point(f"step{step}_n{n:02d}", new, a.outdir)
                p.desc, p.proxy = desc, (obj, floor, sides, nonu)
                pts.append(p)
            list(pool.map(lambda p: p.stage(), pts))
            pts = [p for p in pts if p.ok]
            evaluate(pts, a.seconds, a.seed, pool, "eval")
            pts.sort(key=lambda p: p.total())
            with open(os.path.join(a.outdir, f"step{step}.csv"), "w") as f:
                f.write("tag,move,proxy_obj,floor,fl,fr,fp,nonunit,L,R,P,total\n")
                for p in pts:
                    f.write(f"{p.tag},{p.desc},{p.proxy[0]:.1f},{p.proxy[1]},{p.proxy[2][0]},{p.proxy[2][1]},{p.proxy[2][2]},{p.proxy[3]},{p.cost['L']},{p.cost['R']},{p.cost['Pt']},{p.total()}\n")
            for p in pts[:5]:
                say(f"   {p.total():4d} = {p.cost['L']} + {p.cost['R']} + {p.cost['Pt']}  proxy {p.proxy[1]} {p.proxy[2]} nu {p.proxy[3]}  {p.desc}")
            say(f"step {step}: best neighbour {pts[0].total()} vs incumbent {inc.total()} ({time.time() - t0:.0f}s)")
            if pts[0].total() < inc.total():
                inc = pts[0]
                say(f"step {step}: ACCEPT {inc.desc} -> {inc.total()}")
            else:
                say(f"step {step}: no improving neighbour; stop")
                break
        # deepen the final point
        say(f"final: deepening {inc.tag} at {a.final_seconds:.0f}s x 2 seeds per side")
        evaluate([inc], a.final_seconds, a.seed + 1, pool, "final")
        evaluate([inc], a.final_seconds, a.seed + 2, pool, "final")
    best = os.path.join(a.outdir, "best")
    os.makedirs(best, exist_ok=True)
    for s in "LRP":
        shutil.copy(inc.sms[s], os.path.join(best, f"best_{s}.sms"))
    for side in ("L", "R", "Pt"):
        text = S.translate(inc.seed_prog[side]) if inc.seed_prog[side].endswith("best.slp") else open(inc.seed_prog[side]).read()
        if side == "Pt":
            text = S.transpose(text)
        open(os.path.join(best, f"best_{side[0]}.slp"), "w").write(text)
    say(f"final: {inc.total()} = {inc.cost} -> {best}/best_{{L,R,P}}.{{sms,slp}}")


if __name__ == "__main__":
    main()
