#!/usr/bin/env python3
"""HKS challenge-3 sweep: does any scheme have a summand with NO
type-3 term?  A type-3 term of summand m is a monomial
alpha_m(a,b) beta_m(b,d) gamma_m(a,d) — i.e. m contributes to some
rhs=1 Brent equation.  Convention-proof: the rhs=1 monomial list is
taken from brent.brent_equations itself, so any layout error would
already break the verify gate.
Usage: python3 chk_type3.py bits FILE...      (.bits, last token = bitstring)
       python3 chk_type3.py tabs DIR          (recursive *.tab, mod-2 reduce)
"""
import glob
import os
import sys

from brent import brent_equations, var_counts, verify_bits
from census23 import load_tab

N1, N2, N3, R = 3, 3, 3, 23
EQS = brent_equations(N1, N2, N3, R)
EQS1 = [mons for mons, rhs in EQS if rhs == 1]
assert len(EQS1) == 27
NA, NB, NG = var_counts(N1, N2, N3, R)


def profile(bits):
    """per-summand count of satisfied type-3 monomials"""
    cnt = [0] * R
    for mons in EQS1:
        for va, vb, vg in mons:
            if bits[va] and bits[vb] and bits[vg]:
                cnt[va // (N1 * N2)] += 1
    return cnt


def tab_to_bits(S):
    bits = [0] * (NA + NB + NG)
    for m, (a, b, c_) in enumerate(S):
        for i in range(9):
            bits[m * 9 + i] = abs(a[i]) & 1
            bits[NA + m * 9 + i] = abs(b[i]) & 1
            bits[NA + NB + m * 9 + i] = abs(c_[i]) & 1
    return bits


def sweep(items, verify_all, label):
    n_bad_verify, n_zero, zero_names = 0, 0, []
    mins = {}
    for i, (name, bits) in enumerate(items):
        if verify_all or i < 200:
            if verify_bits(bits, N1, N2, N3, R, EQS) != 0:
                n_bad_verify += 1
                continue
        cnt = profile(bits)
        m = min(cnt)
        mins[m] = mins.get(m, 0) + 1
        if m == 0:
            n_zero += 1
            zero_names.append(name)
            print(f"*** CHALLENGE-3 SOLVER: {name}  profile {cnt}")
    print(f"{label}: {sum(mins.values())} schemes checked "
          f"({n_bad_verify} failed verify gate)")
    print(f"  min-type3-per-summand histogram: {dict(sorted(mins.items()))}")
    if not n_zero:
        print("  no type-3-free summand anywhere")
    return zero_names


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "bits":
        items = []
        for p in sys.argv[2:]:
            s = open(p).read().split()[-1].strip()
            items.append((p, [int(c) for c in s]))
        sweep(items, True, f"bits ({len(items)} files)")
    elif mode == "tabs":
        paths = sorted(glob.glob(os.path.join(sys.argv[2], "**", "*.tab"),
                                 recursive=True))
        def gen():
            for p in paths:
                S = load_tab(p)
                if S is not None:
                    yield (p, tab_to_bits(S))
        sweep(gen(), False, f"tabs under {sys.argv[2]} ({len(paths)} files)")
