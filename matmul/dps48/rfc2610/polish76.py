#!/usr/bin/env python3
"""Every low-cost R program from the seeded runs, polished under its budget with L and P polished too, scored by
the rounding model.  Deduplicates programs by their forms.  Keeps the best program of each operation count.

  polish76.py OUTDIR [MAXCOST]
"""
import glob, os, re, shutil, subprocess, sys
SP = "/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad"
os.environ.update(LNS_NAIVE="1", PLINOPT_BIN=f"{SP}/plinopt_main/bin", R48_SCRATCH=SP)
D = "/Users/greg/projects/logic/matmul/dps48"
sys.path.insert(0, f"{D}/patel"); sys.path.insert(0, D)
import sweep as SW
from concurrent.futures import ThreadPoolExecutor
out = sys.argv[1]; MAXC = int(sys.argv[2]) if len(sys.argv) > 2 else 76
DD = f"{SP}/plinopt_main/data"; SL = "/Users/greg/projects/logic/target/release/slpopt"
os.makedirs(out, exist_ok=True)
sms = f"{DD}/4x4x4_48_accurate_262_R.sms"
progs = {}
for d in sorted(glob.glob(f"{SP}/td/seeded/a262/S_R_s*")):
    b = os.path.join(d, "best.slp")
    if not os.path.exists(b): continue
    t = SW.translate(b); c = SW.slpcheck(sms, t)
    if c and sum(c) <= MAXC: progs.setdefault(t, (sum(c), os.path.basename(d).split('_')[-1]))
print(len(progs), "distinct programs at cost <=", MAXC, " costs", sorted(v[0] for v in progs.values())[:6])
def model(*names):
    r = subprocess.run([SL, "model"] + list(names), capture_output=True, text=True).stdout
    return float(r.strip().splitlines()[-1].split()[3])
def polish(item):
    t, (cost, s) = item
    w = f"{out}/{s}"; os.makedirs(w, exist_ok=True); p = f"{w}/cur"
    for m in "LRP": shutil.copy(f"{DD}/4x4x4_48_accurate_262_{m}.sms", f"{p}_{m}.sms")
    shutil.copy(f"{DD}/4x4x4_48_accurate_262_L.slp", p + "_L.slp"); shutil.copy(f"{DD}/4x4x4_48_accurate_262_P.slp", p + "_P.slp"); open(p + "_R.slp", "w").write(t)
    w0 = model("x", p)
    for rnd in range(4):
        for m, b in (("R", cost), ("P", 112), ("L", 72)):
            subprocess.run([SL, "search", "--scheme", p, "--matrix", m, "--init", f"{p}_{m}.slp", "--out", f"{w}/new_{m}.slp", "--steps", "30000", "--restarts", "2", "--threads", "1", "--seed", str(rnd + 1), "--maxops", str(b)], capture_output=True, text=True)
            shutil.copy(f"{w}/new_{m}.slp", f"{p}_{m}.slp")
    return s, cost, w0, model("x", p)
with ThreadPoolExecutor(12) as ex:
    res = sorted(ex.map(polish, progs.items()), key=lambda r: (r[3], r[1]))
print("seed  cost  model before polish  after")
for s, c, a, b in res[:14]: print(f"  {s:5s} {c}  {a:.3f}  {b:.3f}")
print("before polish, best", min(r[2] for r in res), " after polish, best", res[0][3], " spread", res[-1][3])
