#!/usr/bin/env python3
"""r=22 probe: drop one product from a verified 23-scheme and use the
594-bit remainder as a repair seed for the r=22 Brent system.

A 23-scheme minus a product is NOT a 22-scheme (its type-3 terms lose
coverage), but it is a structured starting point: fix `nfix` of its bits,
let the solver try to repair the rest. Any solve would be a 22-multiplication
mod-2 scheme — i.e. the open challenge 4.

Usage: python3 drop22.py scheme.bits [--nfix 300] [--secs 30] [--threads 10]
                                     [--anf ../target/release/anf]
"""
import argparse
import subprocess
import sys

from brent import var_counts, verify_bits

NA23, NB23, _ = var_counts(3, 3, 3, 23)


def drop_product(bits, m):
    """621-bit r=23 vector -> 594-bit r=22 vector without product m."""
    a = [bits[i] for i in range(NA23) if i // 9 != m]
    b = [bits[NA23 + i] for i in range(NB23) if i // 9 != m]
    g = [bits[NA23 + NB23 + i] for i in range(207) if i // 9 != m]
    assert len(a) == len(b) == len(g) == 198
    return a + b + g


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("scheme")
    ap.add_argument("--nfix", type=int, default=300)
    ap.add_argument("--secs", type=float, default=30)
    ap.add_argument("--threads", type=int, default=10)
    ap.add_argument("--anf", default="../target/release/anf")
    args = ap.parse_args()

    s = open(args.scheme).read().split()[-1].strip()
    bits = [int(c) for c in s]
    assert verify_bits(bits, 3, 3, 3, 23) == 0, "seed scheme must verify"

    best_overall = None
    for m in range(23):
        v22 = drop_product(bits, m)
        tmp = "/tmp/drop22-seed.bits"
        open(tmp, "w").write("".join(map(str, v22)) + "\n")
        r = subprocess.run(
            [args.anf, "3", "3", "3", "22", "--fix-file", tmp,
             "--nfix", str(args.nfix), "--probsat", "--cb", "2.5",
             "--density", "0.1", "--closure-every", "2048",
             "--seconds", str(args.secs), "--threads", str(args.threads),
             "--seed", str(1000 + m), "--quiet"],
            capture_output=True, text=True)
        line = next((l for l in r.stdout.splitlines()
                     if l.startswith("s ")), "s ??")
        print(f"drop m={m:2d}: {line}", flush=True)
        if "SATISFIABLE" in line:
            for l in r.stdout.splitlines():
                if l.startswith("b "):
                    print(l, flush=True)
            print("!!! r=22 SCHEME FOUND — verify + report immediately",
                  flush=True)
            best_overall = m
    if best_overall is None:
        print("no r=22 scheme from this seed (expected — open problem)",
              flush=True)


if __name__ == "__main__":
    main()
