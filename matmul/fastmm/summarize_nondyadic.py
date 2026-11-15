#!/usr/bin/env python3
"""summarize_nondyadic.py results/nondyadic_*.txt: per size, precision and plan, each variant's exact error
(geometric mean over the instances) relative to rdirect's, the range of the per-instance ratios, and the pass
times (L + R + P, median over instances) relative to rdirect's."""
import sys, re, collections, statistics as st, math
err, tm = collections.defaultdict(dict), collections.defaultdict(dict)
for ln in open(sys.argv[1]):
    m = re.match(r"## (\S+) n=(\d+) (\w) seed=(\d+)", ln)
    if m: v, n, t, seed = m.group(1), int(m.group(2)), m.group(3), int(m.group(4)); continue
    m = re.match(r"(\S+)\s+n=.*split L ([\d.]+) R ([\d.]+) gemm ([\d.]+) P ([\d.]+)\s+plan (\S+).*err64 (\S+)", ln)
    if m:
        key = (n, t, m.group(6))
        err[key].setdefault(v, {})[seed] = float(m.group(7))
        tm[key].setdefault(v, {})[seed] = float(m.group(2)) + float(m.group(3)) + float(m.group(5))
vs = ["nd_ctl", "nd_p2", "nd_nd3", "nd_ndr"]
print(f"{'n':>6} {'':3} {'plan':18} {'rdirect err':>12} " + " ".join(f"{v[3:]:>22}" for v in vs) + "   pass time vs rdirect: " + " ".join(v[3:] for v in vs))
for key in sorted(err):
    e, base = err[key], err[key].get("rdirect", {})
    if not base: continue
    gm = lambda xs: math.exp(sum(math.log(x) for x in xs) / len(xs))
    cells = []
    for v in vs:
        rs = [e[v][s] / base[s] for s in base if s in e.get(v, {})]
        cells.append(f"{gm(rs):6.3f} [{min(rs):5.3f},{max(rs):5.3f}]" if rs else "-")
    tb = st.median(tm[key]["rdirect"].values())
    tc = " ".join(f"{st.median(tm[key][v].values()) / tb:5.2f}" if v in tm[key] and tb > 0 else "  -  " for v in vs)
    print(f"{key[0]:>6} {'f32' if key[1] == 'f' else 'f64'} {key[2]:18} {gm(list(base.values())):12.3e} " + " ".join(f"{c:>22}" for c in cells) + "   " + tc)
