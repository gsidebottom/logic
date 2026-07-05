#!/usr/bin/env python3
"""Q2: are Perminov's 3x3x23 schemes equivalent to any of our 53 NEW finds?
Plus context: dedupe his set, membership vs HKS DB (17,376), vs our four
60-addition class representatives, vs the 4 classics.

Procedure identical to dbcheck.phase_check: fingerprint index (de Groote
invariant), 6 S3 slot-variant lookups, exact equivalent() on collisions.
"""
import glob
import os
import sys
import time

M = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # matmul/
sys.path.insert(0, M)
from equiv import bits_to_summands, equivalent, fingerprint, s3_variants

CACHE = os.path.join(M, "perminov_cache")


def load_bits(path):
    return bits_to_summands([int(c) for c in open(path).read().strip()])


def main():
    # --- our 53 NEW schemes ---
    new_keys = [ln.split(",")[0] for ln in open(f"{M}/novelty_verdicts.csv")
                if ln.startswith("walk-") and ln.split(",")[1].startswith("NEW")]
    assert len(new_keys) == 53, len(new_keys)
    ours = [(k, load_bits(f"{M}/found/{k}.bits")) for k in new_keys]

    # --- Perminov schemes (converted+verified bits) ---
    perm = []
    for p in sorted(glob.glob(f"{CACHE}/bits/*.bits")):
        perm.append((os.path.basename(p)[:-5], load_bits(p)))
    print(f"{len(perm)} perminov schemes, {len(ours)} of our NEW schemes")

    # --- dedupe perminov set pairwise ---
    print("\n== Perminov set: pairwise equivalence ==")
    reps = []          # list of (name, summands)
    for name, s in perm:
        hit = None
        for rn, rs in reps:
            fpb = fingerprint(rs)
            if any(fingerprint(v) == fpb for v in s3_variants(s)):
                if equivalent(s, rs):
                    hit = rn
                    break
        if hit:
            print(f"  {name}  == class of {hit}")
        else:
            reps.append((name, s))
            print(f"  {name}  distinct class rep #{len(reps)}")

    # --- reference sets ---
    named = []
    for p in ("external/stapleton60.bits", "external/i106-orbitbest.bits",
              "external/i106b-orbitbest.bits", "external/i107-orbitbest.bits",
              "seeds/laderman.bits", "seeds/smirnov.bits",
              "seeds/oh-kim-moon.bits", "seeds/courtois-bard-hulme.bits"):
        fp = os.path.join(M, p)
        if os.path.exists(fp):
            named.append((p, load_bits(fp)))
    print(f"\n{len(named)} named reference schemes loaded")

    # --- fingerprint index: DB + named + ours ---
    t0 = time.time()
    fpidx = {}
    for ln in open(f"{M}/dbcache/all_schemes.txt"):
        name, bs = ln.split()
        s = bits_to_summands([int(c) for c in bs])
        fpidx.setdefault(fingerprint(s), []).append(("DB:" + name, s))
    for name, s in named:
        fpidx.setdefault(fingerprint(s), []).append(("REF:" + name, s))
    for name, s in ours:
        fpidx.setdefault(fingerprint(s), []).append(("OURS:" + name, s))
    print(f"index built: {len(fpidx)} fingerprints, {time.time()-t0:.0f}s")

    # --- check each perminov scheme against everything ---
    print("\n== Perminov schemes vs DB + refs + our 53 ==")
    for name, s in perm:
        hits, matches = 0, []
        seen = set()
        for var in s3_variants(s):
            for oname, os_ in fpidx.get(fingerprint(var), []):
                if oname in seen:
                    continue
                seen.add(oname)
                hits += 1
                if equivalent(s, os_):
                    matches.append(oname)
        tag = "; ".join(matches) if matches else "NO MATCH"
        print(f"  {name:20s} fp-hits={hits:4d}  ->  {tag}", flush=True)

    print(f"\ndone in {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
