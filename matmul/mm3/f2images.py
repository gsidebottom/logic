#!/usr/bin/env python3
"""Mod-2 images of harvested rank-23 decompositions in the format of ../hb/hbconvert.py, so
the Hell's Bells tools run on them unchanged: OUT.bits.txt ('name bits', 621-bit brent order:
alpha, beta, gamma blocks of 23 x 9, gamma = our output factor c as stored) and OUT.csv
(hbconvert's columns; floor2 = dA2 + dB2 + dC2 - 13, the basis-change floor from the
distinct nonzero rows mod 2 per leg).  Decompositions with no mod-2 image (a product needs a
1/2) are skipped; identical images are written once.  Then
  ../hb/hbnovelty.py OUT.bits.txt OUT.csv OUT          (classes new to the database)
  ../hb/hblegs.py OUT.bits.txt OUT.verdicts.csv DIR     (exact leg screen against 51)

  f2images.py OUT DUMP ... (or @FILE listing them)
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, ".."))
import classify23 as C  # noqa: E402
from check_new23 import mod2_image  # noqa: E402
from brent import verify_bits  # noqa: E402


def d2(rows):
    s = {tuple(v % 2 for v in r) for r in rows}
    s.discard((0,) * 9)
    return len(s)


def dz(rows):
    s = set()
    for r in rows:
        if any(r):
            first = next(v for v in r if v)
            s.add(tuple(-x for x in r) if first < 0 else tuple(r))
    return len(s)


def main():
    out, args = sys.argv[1], sys.argv[2:]
    paths = [q.strip() for a in args for q in (open(a[1:]) if a.startswith("@") else [a]) if q.strip()]
    seen, rows, skipped = set(), [], 0
    rng = random.Random(1)
    checked = 0
    with open(out + ".bits.txt", "w") as fb:
        for p in paths:
            img, why = mod2_image(C.parse_dump(p))
            if img is None:
                skipped += 1
                continue
            bits = [v % 2 for leg in range(3) for prod in img for v in prod[leg]]
            key = "".join(map(str, bits))
            if key in seen:
                continue
            seen.add(key)
            if checked < 300 and rng.random() < 0.05:
                assert verify_bits(bits, 3, 3, 3, 23) == 0, p
                checked += 1
            name = os.path.basename(os.path.dirname(p)).replace("h_", "") + "-" + os.path.basename(p)[:-4]
            fb.write(name + " " + key + "\n")
            A, B, G = ([prod[leg] for prod in img] for leg in range(3))
            nnz = [sum(1 for r in L for v in r if v % 2) for L in (A, B, G)]
            dA2, dB2, dC2 = d2(A), d2(B), d2(G)
            dAz, dBz, dCz = dz(A), dz(B), dz(G)
            naive = sum(max(sum(1 for v in r if v) - 1, 0) for r in A + B) \
                + sum(max(sum(1 for r in G if r[e]) - 1, 0) for e in range(9))
            rows.append(",".join(map(str, [name, 0, naive, *nnz, dA2, dB2, dC2, dA2 + dB2 + dC2 - 13,
                                           dAz, dBz, dCz, dAz + dBz + dCz - 13])))
    with open(out + ".csv", "w") as f:
        f.write("name,adds_file,adds_naive,nnzA,nnzB,nnzC,dA2,dB2,dC2,floor2,dAz,dBz,dCz,floorz\n")
        f.write("".join(r + "\n" for r in rows))
    print(f"{len(paths)} decompositions: {skipped} need 1/2 (no mod-2 image), {len(rows)} distinct "
          f"mod-2 images written ({checked} spot-checked against the F2 Brent equations)")


if __name__ == "__main__":
    main()
