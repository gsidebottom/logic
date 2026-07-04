#!/usr/bin/env python3
"""Flip-graph walk over mod-2 matrix-multiplication schemes
(Kauers-Moosbauer, arXiv:2212.01175), with a sign-SAT liftability
lottery on every new scheme.

The flip move: two rank-1 summands sharing a factor in the same slot,
    a (x) b (x) c   and   a (x) b' (x) c',
rewrite (validity-preserving, checked here by construction AND by the
Brent verifier on every emitted scheme):
    a (x) (b+b') (x) c   and   a (x) b' (x) (c+c').
Analogous moves for a shared middle or last factor. If any summand's
factor becomes ZERO the summand vanishes: RANK REDUCTION (r -> r-1) —
at 4x4x4 r=47 that would be rank 46, an open-problem event, saved and
announced loudly.

Every new distinct-after-summand-sort scheme is (optionally, default on)
sign-SAT lift-tested: a liftable 4x4x4-47 scheme would beat the rank-48
record over Z. Any LIFTED result is saved and announced loudly.

Usage:
  python3 flip.py --dims 4,4,4,47 --seeds seeds4 --archive found4f
                  [--minutes 30] [--lift-every 1] [--rng 1]
"""
import argparse
import glob
import os
import random
import sys
import time

from brent import var_counts, verify_bits
from canon import canon_key
from lift import lift, z_verify


def load(path, dims):
    s = open(path).read().split()[-1].strip()
    bits = [int(c) for c in s]
    assert verify_bits(bits, *dims) == 0, f"{path} does not verify"
    return bits


def to_summands(bits, dims):
    """list of (a,b,c) factor bitmasks (sa,sb,sg bits each)."""
    n1, n2, n3, r = dims
    na, nb, ng = var_counts(*dims)
    sa, sb, sg = n1 * n2, n2 * n3, n1 * n3
    out = []
    for m in range(r):
        a = b = g = 0
        for k in range(sa):
            a |= bits[m * sa + k] << k
        for k in range(sb):
            b |= bits[na + m * sb + k] << k
        for k in range(sg):
            g |= bits[na + nb + m * sg + k] << k
        out.append([a, b, g])
    return out


def to_bits(summ, dims):
    n1, n2, n3, r = dims
    na, nb, ng = var_counts(*dims)
    sa, sb, sg = n1 * n2, n2 * n3, n1 * n3
    bits = [0] * (na + nb + ng)
    for m, (a, b, g) in enumerate(summ):
        for k in range(sa):
            bits[m * sa + k] = (a >> k) & 1
        for k in range(sb):
            bits[na + m * sb + k] = (b >> k) & 1
        for k in range(sg):
            bits[na + nb + m * sg + k] = (g >> k) & 1
    return bits


def random_flip(summ, rng):
    """apply one random flip in place; returns 'flip', 'reduce', or None
    if no shared-factor pair exists in the sampled attempts."""
    r = len(summ)
    for _ in range(64):
        slot = rng.randrange(3)
        i = rng.randrange(r)
        j = rng.randrange(r)
        if i == j or summ[i][slot] != summ[j][slot] or summ[i][slot] == 0:
            continue
        # shared factor in `slot`; modify the other two slots:
        # (i): other1 += other1(j)   (j): other2 += other2(i)
        o1, o2 = [x for x in (0, 1, 2) if x != slot]
        if rng.random() < 0.5:
            o1, o2 = o2, o1
        summ[i][o1] ^= summ[j][o1]
        summ[j][o2] ^= summ[i][o2]
        if 0 in summ[i] or 0 in summ[j]:
            return "reduce"
        return "flip"
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dims", default="4,4,4,47")
    ap.add_argument("--seeds", default="seeds4")
    ap.add_argument("--archive", default="found4f")
    ap.add_argument("--minutes", type=float, default=30.0)
    ap.add_argument("--kick", type=int, default=20,
                    help="flips between dedupe/lift checkpoints")
    ap.add_argument("--restart-every", type=int, default=400,
                    help="checkpoints before restarting from a random seed")
    ap.add_argument("--lift-every", type=int, default=1,
                    help="lift-test every Nth new scheme (1 = all)")
    ap.add_argument("--rng", type=int, default=1)
    args = ap.parse_args()
    dims = tuple(int(x) for x in args.dims.split(","))
    n1, n2, n3, r = dims

    os.makedirs(args.archive, exist_ok=True)
    rng = random.Random(args.rng)
    pool = {}
    for p in sorted(glob.glob(f"{args.seeds}/*.bits")) + \
            sorted(glob.glob(f"{args.archive}/*.bits")):
        bits = load(p, dims)
        pool[canon_key(bits, *dims)] = p
    print(f"flip walk: dims {dims}, pool {len(pool)}, "
          f"{args.minutes} min", flush=True)

    seeds = [load(p, dims) for p in sorted(glob.glob(f"{args.seeds}/*.bits"))]
    cur = to_summands(seeds[rng.randrange(len(seeds))], dims)
    t0 = time.time()
    nflip = nnew = nlift = nred = ncheck = 0
    while time.time() - t0 < args.minutes * 60:
        for _ in range(args.kick):
            res = random_flip(cur, rng)
            if res == "flip":
                nflip += 1
            elif res == "reduce":
                nred += 1
                red = [s for s in cur if 0 not in s]
                rb = to_bits(red, (n1, n2, n3, len(red)))
                bad = verify_bits(rb, n1, n2, n3, len(red))
                out = (f"{args.archive}/RANK{len(red)}-"
                       f"{nred}.bits")
                open(out, "w").write("".join(map(str, rb)) + "\n")
                print("!" * 60 + f"\nRANK REDUCTION: {r} -> {len(red)} "
                      f"(verify {bad} violated) -> {out}\n" + "!" * 60,
                      flush=True)
                # keep walking on the un-reduced scheme (zero summand is
                # legal in the tensor; restore by re-randomizing)
                cur = to_summands(
                    seeds[rng.randrange(len(seeds))], dims)
                break
        ncheck += 1
        bits = to_bits(cur, dims)
        if verify_bits(bits, *dims) != 0:
            print("FLIP BUG: invalid scheme, restarting", flush=True)
            cur = to_summands(seeds[rng.randrange(len(seeds))], dims)
            continue
        k = canon_key(bits, *dims)
        if k not in pool:
            nnew += 1
            out = f"{args.archive}/flip-{nnew:06d}.bits"
            open(out, "w").write("".join(map(str, bits)) + "\n")
            pool[k] = out
            if args.lift_every and nnew % args.lift_every == 0:
                res = lift(bits, dims)
                nlift += 1
                if res is not None:
                    signs, _ = res
                    assert z_verify(bits, signs, dims) == 0
                    lout = out.replace(".bits", ".LIFTED-RECORD.txt")
                    from lift import pretty
                    open(lout, "w").write(
                        pretty(bits, signs, out, dims))
                    print("!" * 60 + f"\nLIFTABLE rank-{r} SCHEME over Z"
                          f" -> {lout}\n" + "!" * 60, flush=True)
            if nnew % 200 == 0:
                el = time.time() - t0
                print(f"[{el:6.0f}s] {nnew} new schemes, {nlift} "
                      f"lift-tested (0 liftable so far), {nred} "
                      f"reductions seen, {nflip} flips", flush=True)
        if ncheck % args.restart_every == 0:
            cur = to_summands(seeds[rng.randrange(len(seeds))], dims)
    el = time.time() - t0
    print(f"done: {nnew} new schemes, {nlift} lift-tested, {nred} rank"
          f"-reduction events, {nflip} flips in {el:.0f}s", flush=True)


if __name__ == "__main__":
    main()
