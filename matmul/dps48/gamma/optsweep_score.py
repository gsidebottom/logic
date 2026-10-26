# After the sweep: per representative and matrix, every program's operation count (counted from
# the .slp, not the optimizer's stderr), its correctness (PLinOpt SLPchecker against the .sms),
# and the rounding model's error for the best complete (L, R, P) set of each representative,
# beside DPS's published programs and our g16s2o programs.
import glob, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
np.seterr(all="ignore")
import slp_errmodel

D = os.path.join(HERE, "..")
P = f"{D}/plinopt/bin"
OUT = sys.argv[1]
MAT = {"dps": lambda M: f"{D}/plinopt/data/4x4x4_48_accurate_262_{M}.sms",
       "ours": lambda M: f"{D}/gamma/g16s2_{M}.sms"}

def ops(path):
    add = sca = 0
    for line in open(path):
        line = line.strip()
        if ":=" not in line or line.startswith("#"):
            continue
        rhs = line.split(":=", 1)[1].rstrip(";")
        sca += len(re.findall(r"[*/]", rhs))
        toks = re.sub(r"\s+", "", rhs)
        add += sum(1 for k, ch in enumerate(toks) if ch in "+-" and k > 0 and toks[k - 1] not in "(*/+-")
    return add, sca

def check(slp, sms):
    r = subprocess.run([f"{P}/SLPchecker", "-M", sms], stdin=open(slp), capture_output=True, text=True, timeout=120)
    out = (r.stdout + r.stderr).lower()
    return "error" not in out and "fail" not in out and r.returncode == 0

best = {}
for rep in ("dps", "ours"):
    for M in "LRP":
        rows = []
        for slp in sorted(glob.glob(f"{OUT}/{rep}_{M}_*.slp")):
            if os.path.getsize(slp) == 0:
                continue
            a, s = ops(slp)
            ok = check(slp, MAT[rep](M))
            rows.append((a + s, a, s, ok, os.path.basename(slp)))
        rows.sort()
        for t, a, s, ok, name in rows:
            print(f"  {name:28s} {a:4d} + {s:3d} = {t:4d}  {'ok' if ok else 'WRONG'}")
        good = [r for r in rows if r[3]]
        if good:
            best[(rep, M)] = good[0]
print()
for rep in ("dps", "ours"):
    if all((rep, M) in best for M in "LRP"):
        pre = f"{OUT}/best_{rep}"
        for M in "LRP":
            os.system(f"cp {OUT}/{best[(rep, M)][4]} {pre}_{M}.slp")
        tot = sum(best[(rep, M)][0] for M in "LRP")
        a = slp_errmodel.analyse(pre)
        print(f"best sweep programs, {rep} representative: {tot} ops  model L+R {a['lr']:.2f} P {a['p']:.2f} "
              f"worst {a['worst']:.2f} count {a['count']:.1f} size {a['size']:.2f}")
for name, pre in [("DPS's published 262", f"{D}/plinopt/data/4x4x4_48_accurate_262"), ("our g16s2o 445", f"{D}/gamma/slp/g16s2o")]:
    a = slp_errmodel.analyse(pre)
    print(f"{name:40s} model L+R {a['lr']:.2f} P {a['p']:.2f} worst {a['worst']:.2f} count {a['count']:.1f} size {a['size']:.2f}")
