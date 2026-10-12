#!/usr/bin/env python3
"""d-profile for OUR scheme corpus (.bits files, brent.py factor-block
layout: a-row m = bits[9m:9m+9], b-row m = bits[207+9m:...], g-row m =
bits[414+9m:...]): per scheme the distinct-rows-per-leg counts and the
basis-invariant KS floor dA+dB+dC-13, as dprofile.py does for the HKS
tarball.  Also emits .legs files for schemes at floor <= --max-floor,
ready for fbmin.

Usage: dprofile_bits.py legs-outdir max_floor file.bits [file.bits ...]
"""
import pathlib, sys

OUTDIR = pathlib.Path(sys.argv[1])
MAXF = int(sys.argv[2])
OUTDIR.mkdir(parents=True, exist_ok=True)

def d_of(rows):
    return len({r for r in rows if r != "0" * 9})

eligible = []
for path in sys.argv[3:]:
    bits = open(path).read().split()[-1].strip()
    if len(bits) != 621:
        print(f"{path}: skip (len {len(bits)})")
        continue
    legs = [[bits[off + 9 * m: off + 9 * m + 9] for m in range(23)]
            for off in (0, 207, 414)]
    ds = [d_of(l) for l in legs]
    floor = sum(ds) - 13
    name = pathlib.Path(path).stem
    tag = "ELIGIBLE" if floor <= MAXF else ""
    print(f"{name}: d={tuple(ds)} floor={floor} {tag}")
    if floor <= MAXF:
        for leg, nm in zip(legs, "ABC"):
            (OUTDIR / f"{name}_{nm}.legs").write_text("\n".join(leg) + "\n")
        eligible.append((floor, name))
print(f"\n{len(eligible)} eligible (floor <= {MAXF}):",
      sorted(eligible)[:20])
