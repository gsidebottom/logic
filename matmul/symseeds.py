#!/usr/bin/env python3
"""Mine every scheme we have (HKS database tarball, hunt archives, our
corpus) for CYCLIC-INVARIANT rank-23 schemes: multiset(summands) equal
to its image under the de Groote 3-cycle (a,b,c) -> (b,c,a).  Such
schemes have three identical KS legs, so per-step = 3a + 14 and a
floor-achieving leg at d=21 (a=12) would give an automatic 50.  Hits
are copied to the output dir as seeds for the symmetric search; for
each hit the induced product permutation (orbit structure) is printed.

Usage: symseeds.py outdir [dirs-or-tgz...]
"""
import pathlib
import sys
import tarfile

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from equiv import bits_to_summands, s3_variants, summands_to_bits  # noqa: E402

OUT = pathlib.Path(sys.argv[1])
OUT.mkdir(parents=True, exist_ok=True)
SOURCES = sys.argv[2:]


def is_cyclic(summ):
    cyc = s3_variants(summ)[1]
    return sorted(summ) == sorted(cyc)


def orbit_structure(summ):
    cyc = s3_variants(summ)[1]
    idx = {}
    for i, s in enumerate(summ):
        idx.setdefault(s, []).append(i)
    pi = []
    used = {k: 0 for k in idx}
    for s in cyc:
        j = idx[s][used[s] % len(idx[s])]
        used[s] += 1
        pi.append(j)
    fixed = sum(1 for i, j in enumerate(pi) if i == j)
    return fixed


def scan_bits(name, line, nhit):
    line = line.strip()
    if len(line) != 621 or set(line) - {"0", "1"}:
        return nhit
    summ = bits_to_summands([int(c) for c in line])
    if is_cyclic(summ):
        nhit += 1
        dst = OUT / f"sym-{nhit:03d}.bits"
        dst.write_text(line + "\n")
        fx = orbit_structure(summ)
        print(f"CYCLIC: {name} (fixed summands ~{fx}) -> {dst}",
              flush=True)
    return nhit


nhit = 0
nseen = 0
for src in SOURCES:
    p = pathlib.Path(src)
    if src.endswith(".tgz"):
        tf = tarfile.open(src, "r:gz")
        for m in tf:
            if not m.name.endswith(".tab"):
                continue
            # tab -> bits with the gamma transpose
            cur, prods = [], []
            for ln in tf.extractfile(m.name).read().decode().splitlines():
                if "|" not in ln:
                    continue
                parts = [q.split() for q in ln.split("|")]
                if len(parts) != 3 or any(len(g) != 3 for g in parts):
                    continue
                cur.append([[abs(int(v)) % 2 for v in g] for g in parts])
                if len(cur) == 3:
                    prods.append(cur)
                    cur = []
            if len(prods) != 23:
                continue
            bits = ""
            for s in range(3):
                for pr in prods:
                    M = [[pr[r][s][c] for c in range(3)] for r in range(3)]
                    if s == 2:
                        M = [[M[c][r] for c in range(3)] for r in range(3)]
                    bits += "".join(str(M[r][c])
                                    for r in range(3) for c in range(3))
            nseen += 1
            nhit = scan_bits(m.name, bits, nhit)
    elif p.is_dir():
        for f in sorted(p.glob("*.bits")):
            nseen += 1
            nhit = scan_bits(str(f), f.read_text().split()[-1], nhit)
    if nseen and nseen % 5000 < 1:
        print(f"[{nseen} scanned, {nhit} cyclic]", flush=True)
print(f"done: {nseen} schemes scanned, {nhit} cyclic-invariant.",
      flush=True)
