#!/usr/bin/env python3
"""Novelty of the Hell's Bells 3x3 schemes against the HKS database.

For each converted scheme (hbconvert.py output), the six S3 slot variants
are fingerprinted (equiv.fingerprint, a de Groote invariant) and looked up
in the fingerprint index of the 17,376 database schemes
(../dbcache/all_schemes.txt, built by ../dbcheck.py); every collision is
decided exactly with equiv.equivalent.  Schemes not equivalent to any
database scheme are then clustered among themselves: by canonical
fingerprint first, then exactly within each bucket, so the class count
is exact.

Output: OUT_PREFIX.verdicts.csv (name, verdict, db_name_or_class_id,
floor2) and a summary on stdout.

Usage: hbnovelty.py HB_BITS_TXT HB_CSV OUT_PREFIX
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + "/..")
from equiv import bits_to_summands, equivalent, fingerprint, s3_variants  # noqa: E402

M = os.path.dirname(os.path.abspath(__file__)) + "/.."


def main():
    bits_txt, csv_in, out = sys.argv[1], sys.argv[2], sys.argv[3]
    t0 = time.time()
    fpidx = {}
    ndb = 0
    for ln in open(f"{M}/dbcache/all_schemes.txt"):
        name, bs = ln.split()
        s = bits_to_summands([int(c) for c in bs])
        fpidx.setdefault(fingerprint(s), []).append((name, s))
        ndb += 1
    print(f"DB: {ndb} schemes, {len(fpidx)} distinct fingerprints ({time.time() - t0:.0f}s)", flush=True)
    floor2 = {}
    for ln in open(csv_in):
        f = ln.rstrip("\n").split(",")
        if f[0] != "name":
            floor2[f[0]] = int(f[9])
    rows = []
    new = []  # (name, summands, canonical fp)
    nhit = 0
    t1 = time.time()
    for i, ln in enumerate(open(bits_txt)):
        name, bs = ln.split()
        summ = bits_to_summands([int(c) for c in bs])
        variants = list(s3_variants(summ))
        fps = [fingerprint(v) for v in variants]
        verdict, detail = "NEW", ""
        for fp in fps:
            for dbname, s2 in fpidx.get(fp, []):
                if equivalent(summ, s2):
                    verdict, detail = "DB", dbname
                    break
            if verdict == "DB":
                break
        if verdict == "DB":
            nhit += 1
        else:
            new.append((name, summ, min(fps)))
        rows.append([name, verdict, detail])
        if (i + 1) % 1000 == 0:
            print(f"  {i + 1} schemes: {nhit} in the DB, {len(new)} new ({time.time() - t1:.0f}s)", flush=True)
    # cluster the new schemes into exact classes
    buckets = {}
    for name, summ, fp in new:
        buckets.setdefault(fp, []).append((name, summ))
    cls_of = {}
    ncls = 0
    for fp, members in buckets.items():
        reps = []  # (class id, summands)
        for name, summ in members:
            for cid, s2 in reps:
                if equivalent(summ, s2):
                    cls_of[name] = cid
                    break
            else:
                ncls += 1
                reps.append((ncls, summ))
                cls_of[name] = ncls
    for r in rows:
        if r[1] == "NEW":
            r[2] = f"class{cls_of[r[0]]:04d}"
    with open(out + ".verdicts.csv", "w") as f:
        f.write("name,verdict,detail,floor2\n")
        for r in rows:
            f.write(",".join(r + [str(floor2.get(r[0], ""))]) + "\n")
    hist_new, hist_db = {}, {}
    for r in rows:
        h = hist_new if r[1] == "NEW" else hist_db
        h[floor2.get(r[0])] = h.get(floor2.get(r[0]), 0) + 1
    print(f"{len(rows)} schemes: {nhit} equivalent to a DB scheme, {len(new)} new in {ncls} exact classes "
          f"({len(buckets)} fingerprint buckets)  ({time.time() - t0:.0f}s)")
    print("floor2 histogram, DB-equivalent:", dict(sorted(hist_db.items())))
    print("floor2 histogram, new:          ", dict(sorted(hist_new.items())))
    best = sorted({cls_of[n]: floor2[n] for n, _, _ in new}.items(), key=lambda t: t[1])[:12]
    print("lowest-floor new classes (class, floor2):", best)


if __name__ == "__main__":
    main()
