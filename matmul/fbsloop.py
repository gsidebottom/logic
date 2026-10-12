#!/usr/bin/env python3
"""Signed model loop: the ring-valid decider for a KS-model addition
count.  For each SAT-enumerated sign model of a mask scheme, run the
SIGNED free-basis search (fbsmin, free mode) on each leg.

Over a ring with free negation the three legs decouple completely:
leg cost is invariant under per-row sign flips (flipping a chain
value's use is a free -1 coefficient), and the per-product balance
eps_u*eps_v*eps_w = +1 is realized by absorbing eps_u*eps_v into the
use of the C value -- also free.  So a model's ring-valid per-step
total is freeA + freeB + freeC + 14, and no cross-leg sign
bookkeeping exists.  (The same argument makes the result model-
independent EXCEPT through row support patterns: models whose shared-
mask rows are +-proportional give d=20 legs; others give d>20.)

Scope caveat inherited from fbsmin: searches 9-target-basis
configurations (0-3 helpers); free-non-target-vector bases are
unbounded over Z and out of scope, so "no" is qualified, "yes" is a
complete ring-valid certificate.

Usage: fbsloop.py bits-file fbsmin-binary workdir [nmodels] [threads]
         [targetA targetB targetC]
"""
import re, subprocess, sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from lift import lift_models, z_verify  # noqa: E402

BITSF, FBSMIN, WORK = sys.argv[1:4]
NMODELS = int(sys.argv[4]) if len(sys.argv) > 4 else 128
THREADS = sys.argv[5] if len(sys.argv) > 5 else "6"
TARGETS = ([int(x) for x in sys.argv[6:9]] if len(sys.argv) > 8 else [12, 13, 12])
DIMS = (3, 3, 3, 23)

bits = [int(c) for c in open(BITSF).read().split()[-1].strip()]
assert len(bits) == 621

def rows_of(signs):
    coef = [signs.get(v, 0) if bits[v] else 0 for v in range(621)]
    return [[tuple(coef[off + m * 9 + k] for k in range(9)) for m in range(23)]
            for off in (0, 207, 414)]

def write_slegs(path, rows):
    with open(path, "w") as f:
        for r in rows:
            f.write(" ".join(str(x) for x in r) + "\n")

def run_leg(path, max_helpers):
    out = subprocess.run(
        [FBSMIN, "--threads", THREADS, "--max-helpers", str(max_helpers), path],
        capture_output=True, text=True).stdout
    m = re.search(r"d=(\d+) min_adds(>?=)(\d+) \[(.*?)\]", out)
    assert m, out[:200]
    d, op, val = int(m.group(1)), m.group(2), int(m.group(3))
    return (val if op == "=" else -val), d, out

models = lift_models(bits, NMODELS, DIMS)
from gaugecanon import dedup_models
models = dedup_models(models, bits)
print(f"{len(models)} gauge-distinct sign models; leg targets {TARGETS} "
      f"(ring total {sum(TARGETS) + 14})", flush=True)

best = None
for mi, (signs, _) in enumerate(models):
    assert z_verify(bits, signs, DIMS) == 0, f"model {mi} fails Z-verify"
    rows = rows_of(signs)
    legs, outs, ok = [], [], True
    for side, nm in enumerate("ABC"):
        path = f"{WORK}/m{mi}_{nm}.slegs"
        write_slegs(path, rows[side])
        # helper budget: target minus the d=20 floor (11); a model whose
        # leg has d>20 then simply cannot reach the target and is skipped
        v, d, out = run_leg(path, max(0, TARGETS[side] - 11))
        legs.append(v)
        outs.append(out)
        if v != TARGETS[side]:
            print(f"model {mi}: {nm} {'=' if v > 0 else '>='}{abs(v)} "
                  f"!= {TARGETS[side]}; skip rest", flush=True)
            ok = False
            break
    if not ok:
        continue
    print(f"\n*** MODEL {mi}: RING-VALID per-step {sum(TARGETS) + 14} ***",
          flush=True)
    for nm, out in zip("ABC", outs):
        print(f"----- {nm} -----\n{out}", flush=True)
    sys.exit(0)

print("no model cleared all three legs at the targets", flush=True)
sys.exit(2)
