# Summarize campaign_var.sh's logs: the variant's error divided by accurate_262's on the same
# inputs, per setting and level (mean [min, max] over seeds), and overall per level.
#   python3 summarize_var.py NAME
import os, sys, collections
sys.path.insert(0, "/Users/greg/projects/logic/matmul/fastmm")
from paper_acc262 import parse

NAME = sys.argv[1]
SP = "/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad"
VAR, REF = f"bench_fmm_var_{NAME}", "bench_fmm_acc262"
LEVELS = {"D48/G": 1, "D48/D48/G": 2, "D48/D48/D48/G": 3, "D48/D48/D48/D48/G": 4, "D48/D48/D48/D48/D48/G": 5}

def table(log, title):
    if not os.path.exists(log):
        print(f"{title}: no log yet"); return
    err = parse(log)
    print(f"== {title} ==")
    overall = collections.defaultdict(list)
    bysetting = collections.defaultdict(lambda: collections.defaultdict(list))
    for (b, t, n, dist, seed), r in err.items():
        if b != REF:
            continue
        rv = err.get((VAR, t, n, dist, seed), {})
        for plan, lv in LEVELS.items():
            if plan in r and plan in rv and r[plan] > 0:
                q = rv[plan] / r[plan]
                overall[lv].append(q); bysetting[(t, n, dist)][lv].append(q)
    for (t, n, dist) in sorted(bysetting):
        cells = []
        for lv in sorted(LEVELS.values()):
            v = bysetting[(t, n, dist)][lv]
            cells.append(f"L{lv} {sum(v)/len(v):.3f} [{min(v):.2f},{max(v):.2f}]" if v else f"L{lv} --")
        print(f"  {t} n={n:<5} {dist:8} " + "  ".join(cells))
    print("  overall: " + "  ".join(f"L{lv} {sum(v)/len(v):.3f} [{min(v):.2f},{max(v):.2f}] (n={len(v)})" for lv, v in sorted(overall.items()) if v))
    # absolute error as a multiple of the classical GEMM's, for both
    for b in (REF, VAR):
        rows = []
        for lv_plan, lv in LEVELS.items():
            vals = []
            for (bb, t, n, dist, seed), r in err.items():
                if bb == b and lv_plan in r and "G" in r and r["G"] > 0 and t == "f":
                    vals.append(r[lv_plan] / r["G"])
            if vals:
                rows.append(f"L{lv} {sum(vals)/len(vals):.2f}")
        print(f"  {b:22} f32 error / classical: " + "  ".join(rows))

table(f"{SP}/camp_{NAME}.log", f"main campaign ({NAME} / accurate_262)")
table(f"{SP}/deep_{NAME}.log", f"deep recursion n=1024 ({NAME} / accurate_262)")
sp = f"{SP}/speed_{NAME}.log"
if os.path.exists(sp):
    import re
    t = collections.defaultdict(list)
    cur = None
    for line in open(sp):
        m = re.match(r"## speed (\S+) round (\d) (\S) (\d+)", line)
        if m:
            cur = (m.group(1), m.group(3), m.group(4)); continue
        m = re.search(r"min\s+([\d.]+) s.*plan (\S+)", line)
        if m and cur:
            t[cur + (m.group(2),)].append(float(m.group(1)))
    print("== speed (best of the rounds) ==")
    for key in sorted({k[1:] for k in t}):
        a = min(t[(REF,) + key]); b = min(t[(VAR,) + key])
        print(f"  {key[0]} n={key[1]} {key[2]:16} acc262 {a:.3f} s  {NAME} {b:.3f} s  ratio {b/a:.3f}")
