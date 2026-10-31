#!/usr/bin/env python3
"""Second pass of the side-cost table: reprice every matrix at or below CUT with a longer run and a new seed, keep the
better cost, and reprint the table.  Costs are lns48's own count here; finalists are verified by sweep.py.

  table48b.py OUTDIR CUT WALL SEED
"""
import json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
outd, CUT, WALL, SEED = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
LNS = "/Users/greg/projects/logic/target/release/lns48"
d = json.load(open(f"{outd}/pairs.json")); classes, res = d["classes"], d["res"]
name = f"{outd}/cost.json"
cost = json.load(open(name))
keys = sorted(k for k, c in cost.items() if c and c <= CUT)
print(len(keys), "matrices to reprice", flush=True)
def price(k):
    out = f"{outd}/lns2/{k}_s{SEED}"; os.makedirs(out, exist_ok=True)
    r = subprocess.run([LNS, "--sms", f"{outd}/uniq/{k}.sms", "--out", out, "--wall", str(WALL), "--seeds", "1", "--seed", str(SEED), "--log", "1e9"], capture_output=True, text=True, timeout=WALL + 200)
    m = re.search(r"final: best (\d+)", r.stdout + r.stderr)
    return k, int(m.group(1)) if m else None
t0 = time.time()
with ThreadPoolExecutor(12) as ex:
    for k, c in ex.map(price, keys):
        if c and c < cost[k]: cost[k] = c
json.dump(cost, open(name, "w"))
rows = []
for ci, bi, kl, kr, cl, cr, dd in res:
    tag, p, _ = classes[ci]
    if cost.get(kl) and cost.get(kr): rows.append((cost[kl] + cost[kr] + p, cost[kl], cost[kr], p, cl, cr, tag, bi))
rows.sort()
print("best triples:")
for r in rows[:14]: print(f"  {r[0]}  L {r[1]} R {r[2]} P {r[3]}  canonical L,R {r[4]},{r[5]}  {r[6]} B{r[7]}")
print("per class, best total, best L alone, best R alone:")
for ci, (tag, p, _) in enumerate(classes):
    v = [r for r in rows if r[6] == tag]
    print(f"  {tag:14s} P {p}: total {min(r[0] for r in v)}, min L {min(r[1] for r in v)}, min R {min(r[2] for r in v)}, min L + min R + P {min(r[1] for r in v) + min(r[2] for r in v) + p}")
print(f"# done {time.time() - t0:.0f} s")
