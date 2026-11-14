#!/usr/bin/env python3
"""Can the low-exponent large square schemes of Sedoglavic's table make a faster, equally accurate level?

Best-case price of ONE <g x g x g : r> level over G6 leaves at n = 13824 (2026-11-12), against the
measured planner picks.  Generous on purpose: the passes are priced at the 64-stream bandwidth the
calibration measures for D48 (~130 GB/s), though these levels need g^2 + r = 400-15000 streams and
the 118-stream 5x5 passes already ran at half of it; leaf GEMMs at the calibration's G6 rate for the
leaf size; padding ignored.

Accuracy: relative error ~ A * sqrt(k_leaf) with A the level's amplification over classical (model of
the report, Section 4).  The 13824 f32 pick R336+2/R363/G6 has A ~ 2.36 * 2.55 (amp ratios per level)
at k_leaf = 768; equal error needs A <= that * sqrt(768 / k_leaf), reported per 4x4-equivalent saving
(amp_eq, the menu's column; accurate_262 2.83, DPS's 3x3x6 point 2.28, its class floor ~2.24).
"""
import math

N = 13824
BW = 130e9                                     # bytes/s, D48 passes, calib5_*.txt
RATE = {"f32": {432: 3.08e12, 576: 3.3e12, 864: 3.66e12, 1728: 3.33e12},   # G6D48 per-product rates;
        "f64": {432: 0.907e12, 576: 0.92e12, 864: 0.936e12, 1728: 0.886e12}}  # 576 interpolated
PICK = {"f32": (0.925, 0.901), "f64": (3.293, 3.238)}   # auto pick, fastest measured (final campaign)
W = {"f32": 4, "f64": 8}

def rate(p, b):
    ks = sorted(RATE[p])
    if b <= ks[0]: return RATE[p][ks[0]]
    for a, c in zip(ks, ks[1:]):
        if b <= c:
            t = (math.log(b) - math.log(a)) / (math.log(c) - math.log(a))
            return math.exp((1 - t) * math.log(RATE[p][a]) + t * math.log(RATE[p][c]))
    return RATE[p][ks[-1]]

A_PICK = 2.36 * 2.55 * math.sqrt(768)          # amp x sqrt(k_leaf) of the 13824 f32 pick
SCHEMES = [(32, 14196, "table"), (30, 11889, "table"), (24, 6488, "table"), (20, 3994, "table"),
           (18, 3031, "table"), (16, 2236, "table"), (32, 15096, "PLinOpt file, amp_eq 7.21 measured"),
           (54, 64000, "our 3x3x6 cycle as one level (reference)")]

print(f"n = {N}; passes at {BW/1e9:.0f} GB/s (64-stream rate, optimistic); picks f32 {PICK['f32']}, f64 {PICK['f64']}")
print(f"{'scheme':>18} {'omega':>7} {'saving':>6} {'leaf':>5} {'traffic':>7} {'streams':>7} "
      f"{'f32 s':>6} {'vs best':>7} {'f64 s':>6} {'vs best':>7} {'amp_eq needed':>13}  note")
for g, r, note in SCHEMES:
    b = math.ceil(N / g); saving = r / g ** 3
    traffic = 3 + 3 * r / g ** 2               # words per n^2, eq. (traffic) of the report
    row = []
    for p in ("f32", "f64"):
        t = r * 2 * b ** 3 / rate(p, b) + traffic * N * N * W[p] / BW
        row.append((t, t / PICK[p][1]))
    eq = math.log(saving) / math.log(0.75)
    need = (A_PICK / math.sqrt(b)) ** (1 / eq)
    omega = 3 * math.log(r) / math.log(g ** 3)
    print(f"<{g}x{g}x{g}:{r}>".rjust(18), f"{omega:7.4f} {saving:6.3f} {b:5d} {traffic:7.1f} {g*g+r:7d} "
          f"{row[0][0]:6.3f} {row[0][1]:7.3f} {row[1][0]:6.3f} {row[1][1]:7.3f} {need:13.2f}  {note}")
