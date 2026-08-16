#!/usr/bin/env python3
"""Uniform PLinOpt measurement with a CORRECT op counter.
(The inherited awk counter stripped +/- before testing for a leading
unary minus, so unary negations were counted as operations.)"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
P = f"{HERE}/../dps48/plinopt/bin"
ENV = dict(os.environ, DYLD_LIBRARY_PATH=f"{HERE}/../dps48/stack/lib")

def ops(slp):
    a = m = 0
    for ln in slp.splitlines():
        if ":=" not in ln: continue
        r = ln.split(":=", 1)[1].replace(" ", "")
        n = r.count("+") + r.count("-")
        if r.startswith("-"): n -= 1     # leading unary negation is free
        a += n; m += r.count("*")
    return a + m

def best(f, reps=12):
    b = None
    for _ in range(reps):
        for mode in ("d", "k"):
            try:
                if mode == "d":
                    o = subprocess.run([f"{P}/optimizer", f], capture_output=True,
                                       text=True, env=ENV, timeout=180).stdout
                else:
                    t = subprocess.run([f"{P}/matrix-transpose", f], capture_output=True,
                                       text=True, env=ENV, timeout=180).stdout
                    k = subprocess.run([f"{P}/optimizer", "-K"], input=t, capture_output=True,
                                       text=True, env=ENV, timeout=180).stdout
                    o = subprocess.run([f"{P}/transpozer"], input=k, capture_output=True,
                                       text=True, env=ENV, timeout=180).stdout
            except subprocess.TimeoutExpired:
                continue
            if ":=" not in o:
                if b is None: b = 0      # no arithmetic emitted (e.g. naive sides)
                continue
            v = ops(o)
            if b is None or v < b: b = v
    return b

def family(tag, ks, reps=12):
    bo, bk = None, None
    for k in ks:
        L = best(f"{HERE}/{tag}_o{k}_L.sms", reps)
        R = best(f"{HERE}/{tag}_o{k}_R.sms", reps)
        Pp = best(f"{HERE}/{tag}_o{k}_P.sms", reps)
        if None in (L, R, Pp): continue
        on = R + Pp
        print(f"  {tag} o{k}: L={L} R={R} P={Pp} total={L+R+Pp} online={on}", flush=True)
        if bo is None or on < bo: bo, bk = on, k
    print(f"{tag}: BEST ONLINE {bo} (orientation {bk})", flush=True)
    return bo

if __name__ == "__main__":
    reps = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    for tag in sys.argv[2:]:
        family(tag, range(6), reps)
