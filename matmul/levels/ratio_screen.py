#!/usr/bin/env python3
"""Is there a scheme with a better ratio than <3x3x6:40>, known or within reach?  (2026-11-14)

A fused level <g1 x g2 x g3 : r> keeps s = r / (g1 g2 g3) of the products and moves
T = 3 + s (g1 + g2 + g3) words per n^2; a pass reads and writes max(g_i g_j) + r blocks at once.
Two figures of merit, lower is better:
  T / (1 - s)    traffic per unit of saving: a level pays when n > T w R / (2 (1 - s) B)
                 (R the leaf's flop/s, B the memory bandwidth, w the word size)
  T / -ln(s)     traffic per unit of log-saving: what a deep plan pays per factor of saving
Sedoglavic's table (fmm_sota.json, ranks only) for every format; for the small formats the rank
that would be needed to beat <3x3x6:40> on saving (s < 40/54) against the best known rank.
"""
import json, math, sys
path = sys.argv[1] if len(sys.argv) > 1 else '/Users/greg/Downloads/fmm_sota.json'
d = json.load(open(path))
rank = {tuple(e['format']): e['rank'] for e in d['entries']}
def known(a, b, c):
    f = tuple(sorted((a, b, c)))
    if f in rank: return rank[f]
    if f[0] == 1: return f[1] * f[2]
    return None
def fig(f, r):
    N = f[0] * f[1] * f[2]; s = r / N; T = 3 + s * sum(f)
    return s, T, max(f[0]*f[1], f[1]*f[2], f[0]*f[2]) + r, T / (1 - s), T / -math.log(s)
ref = fig((3, 3, 6), 40)
print(f"# {path}: {d.get('createdAt')}, {len(rank)} formats")
print(f"reference <3x3x6:40>: saving {ref[0]:.4f} traffic {ref[1]:.2f} streams {ref[2]} T/(1-s) {ref[3]:.1f} T/-ln s {ref[4]:.1f}\n")
rows = []
for f, r in rank.items():
    if r >= f[0] * f[1] * f[2]: continue
    s, T, st, m1, m2 = fig(f, r)
    rows.append((m1, m2, f, r, s, T, st))
for cap in (64, 96, 160, 10**9):
    sel = sorted(x for x in rows if x[6] <= cap)[:8]
    print(f"best T/(1-s) with at most {cap if cap < 10**9 else 'any number of'} streams per pass:")
    for m1, m2, f, r, s, T, st in sel:
        print(f"   <{f[0]}x{f[1]}x{f[2]}:{r}>  saving {s:.4f}  traffic {T:6.2f}  streams {st:5d}  T/(1-s) {m1:6.1f}  T/-ln s {m2:6.1f}")
print("\nbest saving per level with at most 64 / 96 / 160 streams:")
for cap in (64, 96, 160):
    sel = sorted((x[4], x) for x in rows if x[6] <= cap)[:5]
    print(f"  <= {cap}: " + ", ".join(f"<{x[2][0]}x{x[2][1]}x{x[2][2]}:{x[3]}> {s:.4f}" for s, x in sel))
print("\nrank needed to beat <3x3x6:40> (s < 0.7407), formats whose passes would stay within 80 streams at that rank:")
print("   format      known  needed  gap  streams at needed   known lower bound on the gap: open")
out = []
for a in range(2, 9):
    for b in range(a, 13):
        for c in range(b, 25):
            N = a * b * c; r = known(a, b, c)
            if r is None: continue
            need = math.ceil(40 / 54 * N) - 1
            while need / N >= 40 / 54: need -= 1
            st = b * c + need
            if st > 80: continue
            out.append((r - need, st, (a, b, c), r, need))
for gap, st, f, r, need in sorted(out)[:24]:
    print(f"   <{f[0]}x{f[1]}x{f[2]}>   {r:5d}  {need:5d}  {gap:3d}  {st:5d}")
