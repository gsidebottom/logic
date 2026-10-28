#!/usr/bin/env python3
"""The fused-pass cost model for plans of rectangular levels on a square n x n product.  A level
<g1 x g2 x g3 : r> on an (M, K, N) product costs its three passes, (g1 g2 + r) blocks of M/g1 x
K/g2, (g2 g3 + r) of K/g2 x N/g3 and (g1 g3 + r) of M/g1 x N/g3 words, plus r sub-products of
shape (M/g1, K/g2, N/g3).  GEMM time is taken proportional to M K N at the rate of the lone
8192^3 f32 GEMM (0.328 s) and pass time proportional to words at the rate of the D48 level's
passes at 8192 (0.027 s for 12 n^2 words); streams above 64 are not penalized here (the 5x5
measurement says they should be).   python3 cost_rect.py [n]"""
import sys
N = float(sys.argv[1]) if len(sys.argv) > 1 else 8192.0
T_GEMM, T_PASS12 = 0.328, 0.027
LEVELS = {"D48": (4, 4, 4, 48), "336": (3, 3, 6, 40), "363": (3, 6, 3, 40), "633": (6, 3, 3, 40), "SW": (2, 2, 2, 7), "555": (5, 5, 5, 93), "346": (3, 4, 6, 54)}

def gemm(M, K, Nn):
    return T_GEMM * (M * K * Nn) / N ** 3

def plan(levels, M, K, Nn):
    if not levels:
        return gemm(M, K, Nn), 0.0
    g1, g2, g3, r = LEVELS[levels[0]]
    m1, k2, n3 = M / g1, K / g2, Nn / g3
    words = (g1 * g2 + r) * m1 * k2 + (g2 * g3 + r) * k2 * n3 + (g1 * g3 + r) * m1 * n3
    passes = T_PASS12 * words / (12 * N * N)
    tg, tp = plan(levels[1:], m1, k2, n3)
    return r * tg, r * tp + passes

base = gemm(N, N, N)
print(f"n = {N:.0f} f32 (model): saving against the lone GEMM; GEMM part + passes")
for lv in ([], ["D48"], ["336"], ["363"], ["SW"], ["D48", "D48"], ["336", "363"], ["336", "D48"], ["D48", "336"], ["SW", "D48"], ["SW", "336"],
           ["D48", "D48", "D48"], ["336", "363", "633"], ["SW", "D48", "D48"], ["SW", "336", "363"], ["346"], ["555"]):
    tg, tp = plan(lv, N, N, N)
    name = "/".join(lv + ["G"])
    g = [LEVELS[x] for x in lv]
    saving = 1.0
    for g1, g2, g3, r in g: saving *= r / (g1 * g2 * g3)
    print(f"  {name:18s} {100 * (1 - (tg + tp) / base):+6.1f}%   gemm {tg:.4f} s + passes {tp:.4f} s   products kept {saving:.3f}")
