#!/usr/bin/env python3
"""The plan doc's fused-pass cost model, evaluated for 3x3 and 4x4 levels at one size, to compare
shapes (no GEMM streams or pipelines; the numbers are relative):

    T(n) = r T_below(n/g) + 3 (g^2 + r) m^2 w / B,   m = n / g,

with the GEMM time scaling as n^3 and the pass term as (g^2 + r) m^2, both anchored on measured
n = 8192 f32 values on the M4 Pro (../fastmm/results/auto_2026-10-24.txt: the classical GEMM
0.328 s; the D48/G plan's L + R + P passes 0.025-0.027 s, and that plan measured 0.274 s against
the model's 0.273).  Sizes not divisible by the shapes are treated as continuous (the library
pads).

  python3 cost3.py [n_gemm_seconds] [pass48_seconds]
"""
import sys

T_GEMM = float(sys.argv[1]) if len(sys.argv) > 1 else 0.328
T_PASS48 = float(sys.argv[2]) if len(sys.argv) > 2 else 0.027
N = 8192.0
SHAPES = {"4x4": (4, 48), "3x3": (3, 23)}


def gemm(n):
    return T_GEMM * (n / N) ** 3


def passes(g, r, m):
    return T_PASS48 * ((g * g + r) * m * m) / ((16 + 48) * (N / 4) ** 2)


def plan(levels, n=N):
    """levels: shape names from the top; the leaf is a GEMM."""
    if not levels:
        return gemm(n)
    g, r = SHAPES[levels[0]]
    return r * plan(levels[1:], n / g) + passes(g, r, n / g)


def main():
    base = gemm(N)
    print(f"n = {N:.0f} f32, GEMM {base:.3f} s; a plan's saving against the lone GEMM:")
    for levels in ([], ["4x4"], ["4x4", "4x4"], ["3x3"], ["3x3", "3x3"], ["3x3", "3x3", "3x3"],
                   ["4x4", "3x3"], ["3x3", "4x4"]):
        t = plan(levels)
        name = "/".join(levels) + "/GEMM" if levels else "GEMM"
        print(f"  {name:22s} {t:.4f} s  {100 * (1 - t / base):+6.1f}%")


if __name__ == "__main__":
    main()
