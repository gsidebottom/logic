#!/usr/bin/env python3
"""Would an accurate <4x4x8:r> level (record r = 95) help?  (2026-11-12)

Replace the TOP level of the measured 13824 picks (an R level, saving 40/54) by <4x4x8:r>.  The part
below scales with the saving (same cost per product flop, an assumption); the top level's passes
change with traffic 3 + r(1/16 + 1/32 + 1/32) and with their stream count 16+r / 32+r / 32+r:
  fused   : at the 64-stream bandwidth (optimistic: 111-127 streams; the 118-stream 5x5 passes ran at half)
  half    : at half of it, as measured for 5x5:93
  split   : each pass cut into output groups of <= 64 streams, each group re-reading the pass's inputs
            (full bandwidth, extra input reads; not built, never measured)
"""
import math
N, BW = 13824, 130e9
PICK = {"f32": (0.925, 4), "f64": (3.293, 8)}   # measured auto picks (final campaign), word size
R_SAVE, R_TRAFFIC = 40 / 54, 11.89

def split_traffic(r):
    t = 0.0
    for nin, nout in ((16, r), (32, r), (32, r)):       # L, R, P passes (block counts; block size n^2/16, n^2/32, n^2/32)
        groups = math.ceil((nin + nout) / 64) if nin + nout > 64 else 1
        while nin + math.ceil(nout / groups) > 64: groups += 1
        size = {16: 1 / 16, 32: 1 / 32}[nin]
        t += (groups * nin + nout) * size
    return t

print(f"n = {N}; top level replaced in the picks (f32 {PICK['f32'][0]} s, f64 {PICK['f64'][0]} s); times relative to the pick")
print(f"{'r':>3} {'omega':>7} {'saving':>7} {'streams':>11} {'traffic':>7} {'split':>6} | "
      f"{'f32 fused':>9} {'half':>6} {'split':>6} | {'f64 fused':>9} {'half':>6} {'split':>6}")
for r in range(96, 84, -1):
    s = r / 128; tr = 3 + r * (1 / 16 + 1 / 32 + 1 / 32); st = split_traffic(r)
    omega = 3 * math.log(r) / math.log(128)
    out = []
    for p in ("f32", "f64"):
        t, w = PICK[p]
        top = R_TRAFFIC * N * N * w / BW
        below = (t - top) * s / R_SAVE
        for traf, bw in ((tr, BW), (tr, BW / 2), (st, BW)):
            out.append((below + traf * N * N * w / bw) / t)
    print(f"{r:3d} {omega:7.4f} {s:7.4f} {16+r:4d}/{32+r}/{32+r} {tr:7.2f} {st:6.2f} | "
          f"{out[0]:9.3f} {out[1]:6.3f} {out[2]:6.3f} | {out[3]:9.3f} {out[4]:6.3f} {out[5]:6.3f}")
print("reference: 4x4x4:48 saving 0.750 traffic 12.00, 3x3x6:40 saving 0.741 traffic 11.89, both <= 64 streams;"
      " omega of 3x3x6:40 = 2.7743 needs r <= 88 at 4x4x8")
