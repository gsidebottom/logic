#!/usr/bin/env python3
"""Do the new Hell's Bells classes coincide with schemes WE found outside the
HKS database?  Index every 3x3 rank-23 .bits scheme under the given
directories by fingerprint (equiv.fingerprint; each scheme Brent-verified
mod 2 as it is loaded), then look up the six slot variants of one
representative per new Hell's Bells class and decide collisions exactly
with equiv.equivalent.

Usage: hbours.py HB_BITS_TXT HB_VERDICTS_CSV OUT_CSV DIR [DIR ...]
"""
import glob
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + "/..")
from brent import brent_equations, verify_bits  # noqa: E402
from equiv import bits_to_summands, equivalent, fingerprint, s3_variants  # noqa: E402

EQS = None


def load(path):
    global EQS
    if EQS is None:
        EQS = brent_equations(3, 3, 3, 23)
    try:
        tok = open(path).read().split()
        if not tok:
            return (path, None, "empty")
        bs = tok[-1]
        if len(bs) != 621 or set(bs) - {"0", "1"}:
            return (path, None, "not-621")
        bits = [int(c) for c in bs]
        if verify_bits(bits, 3, 3, 3, 23, EQS):
            return (path, None, "brent-fail")
        return (path, fingerprint(bits_to_summands(bits)), bs)
    except Exception as e:  # unreadable file
        return (path, None, f"error:{e}")


def main():
    hb_bits, hb_verd, out, dirs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
    t0 = time.time()
    paths = []
    for d in dirs:
        paths += glob.glob(os.path.join(d, "**", "*.bits"), recursive=True)
    paths = sorted(set(paths))
    print(f"{len(paths)} .bits files under {len(dirs)} directories", flush=True)
    idx = {}
    skipped = {}
    nvalid = 0
    with ProcessPoolExecutor(max_workers=8) as ex:
        for i, (path, fp, info) in enumerate(ex.map(load, paths, chunksize=64)):
            if fp is None:
                skipped[info.split(":")[0]] = skipped.get(info.split(":")[0], 0) + 1
            else:
                nvalid += 1
                idx.setdefault(fp, []).append((path, info))
            if (i + 1) % 20000 == 0:
                print(f"  {i + 1} files ({time.time() - t0:.0f}s)", flush=True)
    print(f"indexed {nvalid} valid schemes, {len(idx)} distinct fingerprints; skipped {skipped} ({time.time() - t0:.0f}s)", flush=True)
    bits = {}
    for ln in open(hb_bits):
        name, bs = ln.split()
        bits[name] = bs
    reps = {}
    for ln in open(hb_verd):
        f = ln.rstrip("\n").split(",")
        if f[1] == "NEW" and f[2] not in reps:
            reps[f[2]] = (f[0], int(f[3]))
    rows = ["class,rep,floor2,match,our_file"]
    nmatch = 0
    for cls, (name, fl) in sorted(reps.items()):
        summ = bits_to_summands([int(c) for c in bits[name]])
        match = ""
        for var in s3_variants(summ):
            for path, bs in idx.get(fingerprint(var), []):
                if equivalent(summ, bits_to_summands([int(c) for c in bs])):
                    match = path
                    break
            if match:
                break
        nmatch += bool(match)
        rows.append(f"{cls},{name},{fl},{int(bool(match))},{match}")
    open(out, "w").write("\n".join(rows) + "\n")
    print(f"{len(reps)} new Hell's Bells classes: {nmatch} coincide with a scheme of ours, {len(reps) - nmatch} do not ({time.time() - t0:.0f}s)", flush=True)
    for r in rows[1:]:
        if r.endswith(",1," ) or r.split(",")[3] == "1":
            print("  " + r)


if __name__ == "__main__":
    main()
