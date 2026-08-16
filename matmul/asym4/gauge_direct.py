#!/usr/bin/env python3
"""Gauge search with the TRUE objective: PLinOpt achieved online cost.
Screens gauge images of Strassen^2-49 at low reps, reports the best.
Every image verified by exact evaluation before it is measured."""
import json, os, random, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from mk49 import strassen2, kron, gate, orientations, emit
from gauge import act, rand_unimodular

P = f"{HERE}/../dps48/plinopt/bin"
ENV = dict(os.environ, DYLD_LIBRARY_PATH=f"{HERE}/../dps48/stack/lib")

def ops(slp):
    a = m = 0
    for ln in slp.splitlines():
        if ":=" not in ln: continue
        r = ln.split(":=", 1)[1].replace(" ", "")
        n = r.count("+") + r.count("-")
        if r.startswith("-"): n -= 1
        a += n; m += r.count("*")
    return a + m

def best_ops(f, reps):
    best = None
    for _ in range(reps):
        for mode in ("direct", "kernel"):
            try:
                if mode == "direct":
                    o = subprocess.run([f"{P}/optimizer", f], capture_output=True,
                                       text=True, env=ENV, timeout=120).stdout
                else:
                    t = subprocess.run([f"{P}/matrix-transpose", f], capture_output=True,
                                       text=True, env=ENV, timeout=120).stdout
                    k = subprocess.run([f"{P}/optimizer", "-K"], input=t, capture_output=True,
                                       text=True, env=ENV, timeout=120).stdout
                    o = subprocess.run([f"{P}/transpozer"], input=k, capture_output=True,
                                       text=True, env=ENV, timeout=120).stdout
            except subprocess.TimeoutExpired:
                continue
            if ":=" not in o: continue
            v = ops(o)
            if best is None or v < best: best = v
    return best

def online_of(img, tag, reps):
    """min over orientations of (R + P) with L free."""
    best = None
    for k, (a, b, c) in enumerate(orientations(*img)):
        emit(a, b, c, HERE, f"{tag}_o{k}")
        r = best_ops(f"{HERE}/{tag}_o{k}_R.sms", reps)
        p = best_ops(f"{HERE}/{tag}_o{k}_P.sms", reps)
        for suf in ("L", "R", "P"):
            os.unlink(f"{HERE}/{tag}_o{k}_{suf}.sms")
        if r is None or p is None: continue
        if best is None or r + p < best: best = r + p
    return best

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    reps = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    al, be, ga = kron(*strassen2())
    assert gate(al, be, ga, n=4)
    base = online_of((al, be, ga), "base", reps)
    print(f"Strassen^2-49 baseline online (reps={reps}): {base}", flush=True)
    rng = random.Random(seed)
    best, bestg = base, None
    for t in range(trials):
        Pm, Qm, Rm = (rand_unimodular(rng, rng.choice((1, 1, 2))) for _ in range(3))
        img = act(al, be, ga, Pm, Qm, Rm)
        if img is None: continue
        if not gate(*img, n=4): continue
        v = online_of(img, f"t{t}", reps)
        if v is not None and v < best:
            best, bestg = v, {"P": Pm, "Q": Qm, "R": Rm}
            print(f"  trial {t}: NEW BEST online {v}", flush=True)
    print(f"best online {best} (baseline {base})")
    if bestg:
        json.dump(bestg, open(f"{HERE}/gauge_direct_best_s{seed}.json", "w"))
