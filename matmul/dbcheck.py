#!/usr/bin/env python3
"""Reproduce the full-database novelty check from primary sources.

Downloads the Kauers/Heule/Seidl scheme archive (schemes.tgz, ~43 MB),
converts every .tab file (17,376 found schemes + the 4 classics) to our
bit format with a verify-everything gate, then checks every local find
against ALL of them: fingerprint index first (a de-Groote invariant, all
6 S3 slot-variants), exact `equivalent()` on any collision. This is
directory-scope-free and therefore strictly stronger than pattern-scoped
sweeps: a NEW verdict here does not depend on the rank-pattern legend.

Phases (run in order; each is idempotent/cached):
  python3 dbcheck.py fetch      # download schemes.tgz -> dbcache/
  python3 dbcheck.py convert    # .tab -> bits, verify_bits==0 gate
  python3 dbcheck.py controls   # 20 db-seeds byte-identical + classics
  python3 dbcheck.py check      # verdict per found/walk-*.bits
  python3 dbcheck.py all        # all of the above

Outputs dbcache/all_schemes.txt (name + bits per line) and
dbcache/verdicts_full.csv; compare the latter's verdict column against
the committed novelty_verdicts.csv.
"""
import glob
import os
import ssl
import sys
import tarfile
import time
import urllib.request

from brent import verify_bits
from equiv import bits_to_summands, equivalent, fingerprint, s3_variants

M = os.path.dirname(os.path.abspath(__file__))
CACHE = f"{M}/dbcache"
TGZ = f"{CACHE}/schemes.tgz"
ALL = f"{CACHE}/all_schemes.txt"
URL = ("https://www.algebra.uni-linz.ac.at/research/"
       "matrix-multiplication/schemes.tgz")


def tab_to_bits(lines):
    """.tab lines -> 621-char bit string (mod 2; C block transposed —
    convention validated against 13 byte-identical seed anchors and
    0/17,376 verify failures; see seeds/README.md)."""
    blocks, cur = [], []
    for line in lines:
        if line.lstrip().startswith("---"):
            if cur:
                blocks.append(cur)
                cur = []
            continue
        if line.strip():
            cur.append(line)
    if cur:
        blocks.append(cur)
    if len(blocks) != 23:
        raise ValueError(f"{len(blocks)} blocks (want 23)")
    bits = ["0"] * 621
    for m, blk in enumerate(blocks):
        if len(blk) != 3:
            raise ValueError(f"block {m}: {len(blk)} rows")
        for r_i, line in enumerate(blk):
            parts = line.split("|")
            if len(parts) != 3:
                raise ValueError(f"block {m} row {r_i}")
            for g_i, grp in enumerate(parts):
                vals = grp.split()
                if len(vals) != 3:
                    raise ValueError(f"block {m} row {r_i} grp {g_i}")
                for c_i, v in enumerate(vals):
                    if int(v) & 1:
                        if g_i == 0:
                            bits[m * 9 + r_i * 3 + c_i] = "1"
                        elif g_i == 1:
                            bits[207 + m * 9 + r_i * 3 + c_i] = "1"
                        else:  # C transposed: (x,y) contributes to C[y][x]
                            bits[414 + m * 9 + c_i * 3 + r_i] = "1"
    return "".join(bits)


def phase_fetch():
    os.makedirs(CACHE, exist_ok=True)
    if os.path.exists(TGZ) and os.path.getsize(TGZ) > 1 << 20:
        print(f"fetch: {TGZ} already present "
              f"({os.path.getsize(TGZ) >> 20} MB)")
        return
    ctx = ssl.create_default_context()
    ctx.check_hostname = False           # site TLS cert is expired
    ctx.verify_mode = ssl.CERT_NONE
    print(f"fetch: downloading {URL} ...")
    req = urllib.request.Request(
        URL, headers={"User-Agent": "matmul-novelty-check/1.0"})
    with urllib.request.urlopen(req, timeout=300, context=ctx) as r:
        data = r.read()
    open(TGZ, "wb").write(data)
    print(f"fetch: {len(data) >> 20} MB")


def phase_convert():
    n_ok = n_fail = 0
    t0 = time.time()
    with tarfile.open(TGZ) as tf, open(ALL, "w") as out:
        for mem in tf:
            if not mem.name.endswith(".tab"):
                continue
            name = os.path.basename(mem.name)[:-4]
            lines = tf.extractfile(mem).read().decode().splitlines()
            try:
                bs = tab_to_bits(lines)
                if verify_bits([int(c) for c in bs], 3, 3, 3, 23) != 0:
                    raise ValueError("verify_bits != 0")
                out.write(f"{name} {bs}\n")
                n_ok += 1
            except Exception as e:
                n_fail += 1
                print(f"  FAIL {mem.name}: {e}")
            if n_ok % 4000 == 0 and n_ok:
                print(f"  {n_ok} converted, {time.time()-t0:.0f}s",
                      flush=True)
    print(f"CONVERT: {n_ok} valid, {n_fail} failures")
    if n_fail:
        sys.exit("parse failures — converter suspect, stop")


def load_all():
    return [(ln.split()[0], ln.split()[1])
            for ln in open(ALL) if ln.strip()]


def phase_controls():
    db = dict(load_all())
    n = 0
    for path in sorted(glob.glob(f"{M}/seeds/db-*.bits")):
        key = os.path.basename(path)[3:-5]
        ours = open(path).read().strip()
        assert key in db, f"{key} missing from archive"
        assert db[key] == ours, f"{key}: bits differ from our seed copy"
        n += 1
    # classics present and equivalent to our embedded/seed copies
    for cname in ("laderman", "smirnov", "oh-kim-moon",
                  "courtois-bard-hulme"):
        assert cname in db, f"classic {cname} missing"
        s_db = bits_to_summands([int(c) for c in db[cname]])
        s_us = bits_to_summands(
            [int(c) for c in open(f"{M}/seeds/{cname}.bits").read().strip()])
        assert equivalent(s_us, s_db), f"classic {cname}: not equivalent"
        n += 1
    print(f"CONTROLS: {n} passed (20 byte-identical db seeds + 4 classics)")


def phase_check():
    t0 = time.time()
    entries = load_all()
    print(f"indexing {len(entries)} DB schemes by fingerprint ...")
    fpidx = {}
    for name, bs in entries:
        s = bits_to_summands([int(c) for c in bs])
        fpidx.setdefault(fingerprint(s), []).append((name, s))
    print(f"  {len(fpidx)} distinct fingerprints, {time.time()-t0:.0f}s")
    rows = []
    for path in sorted(glob.glob(f"{M}/found/walk-*.bits")):
        key = os.path.basename(path)[:-5]
        summ = bits_to_summands(
            [int(c) for c in open(path).read().strip()])
        verdict, detail, fp_hits = "NEW-vs-DB", "", 0
        for var in s3_variants(summ):
            for name, s2 in fpidx.get(fingerprint(var), []):
                fp_hits += 1
                if equivalent(summ, s2):
                    verdict, detail = "EQUIVALENT", name
                    break
            if verdict == "EQUIVALENT":
                break
        if verdict == "NEW-vs-DB":
            detail = f"fp-hits={fp_hits}"
        rows.append((key, verdict, detail))
        print(f"  {key}: {verdict} {detail}", flush=True)
    out = f"{CACHE}/verdicts_full.csv"
    with open(out, "w") as f:
        f.write("find,verdict,detail\n")
        for r in rows:
            f.write(",".join(r) + "\n")
    ne = sum(1 for r in rows if r[1] == "EQUIVALENT")
    print(f"CHECK: {ne} EQUIVALENT / {len(rows)-ne} NEW-vs-DB -> {out}")
    # cross-check against the committed verdicts if present
    committed = f"{M}/novelty_verdicts.csv"
    if os.path.exists(committed):
        want = {ln.split(",")[0]: ln.split(",")[1]
                for ln in open(committed) if ln.startswith("walk-")}
        mism = [k for k, v, _ in rows if want.get(k) not in (None, v)]
        print(f"cross-check vs committed novelty_verdicts.csv: "
              f"{'MATCH' if not mism else f'MISMATCH {mism}'}")


if __name__ == "__main__":
    phases = sys.argv[1:] or ["all"]
    if phases == ["all"]:
        phases = ["fetch", "convert", "controls", "check"]
    for ph in phases:
        {"fetch": phase_fetch, "convert": phase_convert,
         "controls": phase_controls, "check": phase_check}[ph]()
