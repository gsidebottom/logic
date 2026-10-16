#!/usr/bin/env python3
"""Generate the variable-orbit map for the cyclic-symmetric ansatz:
rank-23 schemes invariant under the de Groote 3-cycle
(a,b,c) -> (b,c,a) with product orbits (3j, 3j+1, 3j+2) for j < 7 and
products 21, 22 fixed.

The bit-level slot/cell permutation tau is extracted NUMERICALLY from
equiv.py's validated maps: for each of the 621 bits, push a single-bit
scheme through bits_to_summands -> 3-cycle -> summands_to_bits and
read off where the bit lands (the cycle is per-summand, so a single
bit maps to a single bit, product index unchanged).  The full action
g = product-permutation o tau; its orbits must all have size 3,
giving 207 orbit variables.  Output: lines "var rep" for every var,
rep = orbit minimum.

Usage: symorbits.py out.map
"""
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from equiv import bits_to_summands, s3_variants, summands_to_bits  # noqa: E402

OUT = sys.argv[1]

# tau: slot/cell permutation at fixed product index
tau = [None] * 621
for v in range(621):
    bits = [0] * 621
    bits[v] = 1
    summ = bits_to_summands(bits)
    img = s3_variants(summ)[1]
    out = summands_to_bits(img)
    nz = [i for i, b in enumerate(out) if b]
    assert len(nz) == 1, (v, len(nz))
    tau[v] = nz[0]
assert sorted(tau) == list(range(621)), "tau must be a permutation"

# product permutation pi: 3j -> 3j+1 -> 3j+2 -> 3j; 21, 22 fixed
def pi(m):
    if m >= 21:
        return m
    j, r = divmod(m, 3)
    return 3 * j + (r + 1) % 3

# var layout: block (A/B/C) of 207 = 23 products x 9 cells
def act(v):
    t = tau[v]
    blk, off = divmod(t, 207)
    m, k = divmod(off, 9)
    return blk * 207 + pi(m) * 9 + k

orbits = {}
seen = [False] * 621
norb = 0
for v in range(621):
    if seen[v]:
        continue
    orb = [v]
    w = act(v)
    while w != v:
        orb.append(w)
        w = act(w)
    assert len(orb) == 3, (v, len(orb))
    rep = min(orb)
    for u in orb:
        assert not seen[u]
        seen[u] = True
        orbits[u] = rep
    norb += 1
assert norb == 207
with open(OUT, "w") as f:
    for v in range(621):
        f.write(f"{v} {orbits[v]}\n")
print(f"wrote {OUT}: 621 vars -> {norb} orbits of size 3")
