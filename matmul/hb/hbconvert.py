#!/usr/bin/env python3
"""Convert Hell's Bells 3x3 rank-23 schemes to our 621-bit Brent-order format.

Source: E. Martensson (and coauthors), "Hell's Bells: A Neural Network
Pipeline for Ternary Fast Matrix Multiplication Algorithms", IACR ePrint
2026/1688; data in github.com/werekorren/fmm_add_reduction,
algorithms/hells_bells/333 (15,316 files seedNNN-333-23-ADDS.txt, ADDS =
naive addition count).

File format: three 9x23 integer blocks separated by '#', entries in
{-1, 0, 1}; columns are the 23 products, rows the nine entries of A, B
and C.  The entry order and the C convention are not assumed: for the
first file every combination of row-major/column-major per block is tried
and the one satisfying all 729 integer Brent equations is kept; every
other file must then satisfy them under that convention or is rejected.

Output: OUT.bits.txt (name and 621 bits per line, mod 2, brent.py order:
alpha block, beta block, gamma block, each product-major then row-major)
and OUT.csv with per-scheme counts: naive adds, nonzeros per leg, distinct
nonzero vectors per leg mod 2 (dA2, dB2, dC2) and over Z (dAz, dBz, dCz),
and the basis-change floors floor2 = dA2+dB2+dC2-13 and floorz (see
../dprofile.py).

Usage: hbconvert.py DATADIR OUT_PREFIX
"""
import glob
import itertools
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + "/..")
from brent import verify_bits  # noqa: E402

R = 23
TARGET = np.zeros((3, 3, 3, 3, 3, 3), dtype=np.int64)
for a, b, c, d, p, q in itertools.product(range(3), repeat=6):
    TARGET[a, b, c, d, p, q] = int(b == c and a == p and d == q)


def parse(path):
    blocks, cur = [], []
    for ln in open(path):
        ln = ln.strip()
        if ln == "#":
            blocks.append(cur)
            cur = []
        elif ln:
            cur.append([int(v) for v in ln.split()])
    if cur:
        blocks.append(cur)
    assert len(blocks) == 3, f"{path}: {len(blocks)} blocks"
    arr = [np.array(b, dtype=np.int64) for b in blocks]
    for x in arr:
        assert x.shape == (9, R), f"{path}: block shape {x.shape}"
    return arr


def legs(arr, order):
    """arr: three (9, 23) blocks; order: per block, 'r' (row-major entries)
    or 'c' (column-major).  Returns alpha, beta, gamma as (23, 3, 3)."""
    out = []
    for blk, o in zip(arr, order):
        m = blk.T.reshape(R, 3, 3)  # entry e -> (e // 3, e % 3)
        if o == "c":
            m = m.transpose(0, 2, 1)
        out.append(m)
    return out


def brent_ok(alpha, beta, gamma):
    t = np.einsum("mab,mcd,mpq->abcdpq", alpha, beta, gamma)
    return bool((t == TARGET).all())


def to_bits(alpha, beta, gamma):
    bits = []
    for leg in (alpha, beta, gamma):
        for m in range(R):
            bits.extend(int(v) & 1 for v in leg[m].reshape(9))
    return bits


def d_counts(leg):
    rows2 = {tuple(int(v) & 1 for v in leg[m].reshape(9)) for m in range(R)}
    rows2.discard((0,) * 9)
    rowsz = set()
    for m in range(R):
        r = tuple(int(v) for v in leg[m].reshape(9))
        if any(r):
            first = next(v for v in r if v)
            rowsz.add(tuple(-x for x in r) if first < 0 else r)
    return len(rows2), len(rowsz)


def naive_adds(alpha, beta, gamma):
    a = sum(max(int(np.count_nonzero(alpha[m])) - 1, 0) for m in range(R))
    b = sum(max(int(np.count_nonzero(beta[m])) - 1, 0) for m in range(R))
    c = sum(max(int(np.count_nonzero(gamma[:, p, q])) - 1, 0) for p in range(3) for q in range(3))
    return a, b, c


def main():
    datadir, out = sys.argv[1], sys.argv[2]
    files = sorted(glob.glob(os.path.join(datadir, "*.txt")))
    assert files, "no .txt files"
    # convention from the first file
    arr0 = parse(files[0])
    good = [o for o in itertools.product("rc", repeat=3) if brent_ok(*legs(arr0, o))]
    print(f"{len(files)} files; conventions passing integer Brent on {os.path.basename(files[0])}: {good}")
    assert good, "no convention satisfies Brent"
    order = good[0]
    nbits = 0
    rows = ["name,adds_file,adds_naive,nnzA,nnzB,nnzC,dA2,dB2,dC2,floor2,dAz,dBz,dCz,floorz"]
    bad = 0
    with open(out + ".bits.txt", "w") as fb:
        for f in files:
            name = os.path.basename(f)[:-4]
            alpha, beta, gamma = legs(parse(f), order)
            if not brent_ok(alpha, beta, gamma):
                bad += 1
                print(f"REJECT {name}: fails integer Brent under {order}")
                continue
            bits = to_bits(alpha, beta, gamma)
            if nbits < 50:  # spot-check the mod-2 encoding against brent.py
                assert verify_bits(bits, 3, 3, 3, R) == 0, name
                nbits += 1
            fb.write(name + " " + "".join(map(str, bits)) + "\n")
            (dA2, dAz), (dB2, dBz), (dC2, dCz) = d_counts(alpha), d_counts(beta), d_counts(gamma)
            na, nb, nc = naive_adds(alpha, beta, gamma)
            adds_file = int(name.rsplit("-", 1)[1])
            rows.append(",".join(map(str, [name, adds_file, na + nb + nc,
                                           int(np.count_nonzero(alpha)), int(np.count_nonzero(beta)), int(np.count_nonzero(gamma)),
                                           dA2, dB2, dC2, dA2 + dB2 + dC2 - 13, dAz, dBz, dCz, dAz + dBz + dCz - 13])))
    open(out + ".csv", "w").write("\n".join(rows) + "\n")
    print(f"wrote {len(rows) - 1} schemes to {out}.bits.txt/.csv; rejected {bad}")


if __name__ == "__main__":
    main()
