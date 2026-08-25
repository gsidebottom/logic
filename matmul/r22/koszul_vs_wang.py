#!/usr/bin/env python3
"""Measurement: does our Koszul flattening bound add anything to Wang's
DP (arXiv:2603.07280) on the 3x3 F_2 orbit tensors?

Parses certs/matrix/cert_matrix_q02_n333.pb.txt from
github.com/wcgbg/tensor-rank-lower-bound (clone path below), rebuilds
each orbit's constrained tensor with OUR machinery (his constraint rows
= killed-subspace rows; restricting A to their kernel = our quotient's
annihilator contraction), computes our Koszul bound (p <= 7), and
compares with his recorded rank_lower_bound.

Verdict (2026-08-24): Koszul strictly beats the recorded bound on
exactly 1 of 496 orbits (index 70, dim 6: recorded 13, koszul 14) and
is far below the recorded bounds at the load-bearing dims 0-4
(14-15 vs 17-20): grafting Koszul into his DP is NOT the rank-21 lever.
"""
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from subgame_verify import quotient, flattenings, koszul_bound, matmul_tensor

CERT = "/Users/greg/projects/trlb-wang/certs/matrix/cert_matrix_q02_n333.pb.txt"


def parse_bytes(s):
    out, i = [], 0
    while i < len(s):
        if s[i] == "\\":
            nxt = s[i + 1]
            if nxt in "nrt\"\\'":
                out.append({"n": 10, "r": 13, "t": 9, '"': 34, "\\": 92, "'": 39}[nxt])
                i += 2
            else:
                out.append(int(s[i + 1:i + 4], 8))
                i += 4
        else:
            out.append(ord(s[i]))
            i += 1
    return out


def main():
    txt = open(CERT).read()
    blocks = re.findall(r"constrained_tensors \{(.*?)\n\}", txt, re.S)
    d, t0 = matmul_tensor(3)
    better = []
    n = 0
    for b in blocks:
        lbm = re.search(r"rank_lower_bound: (\d+)", b)
        if lbm is None:
            continue
        lb = int(lbm.group(1))
        cm = re.search(r'constraints: "((?:[^"\\]|\\.)*)"', b)
        U = []
        if cm:
            by = parse_bytes(cm.group(1))
            U = [by[i] | (by[i + 1] << 8) for i in range(0, len(by), 2)]
        dims, t = quotient(d, t0, U, [], [])
        kz = koszul_bound(dims, t, 7)
        n += 1
        if kz > lb:
            idx = int(re.search(r"index: (\d+)", b).group(1))
            better.append((idx, len(U), lb, kz))
    print(f"{n} orbits; koszul beats the recorded bound on {len(better)}: {better}")


if __name__ == "__main__":
    main()
